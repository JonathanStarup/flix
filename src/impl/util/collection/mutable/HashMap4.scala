package impl.util.collection.mutable

import scala.collection.{immutable, mutable}

/**
 * A mutable map with four keys backed by [[scala.collection.mutable.Map]] and [[Map3]].
 */
final class HashMap4[K1, K2, K3, K4, V](m: mutable.Map[K1, Map3[K2, K3, K4, V]] = mutable.Map.empty[K1, Map3[K2, K3, K4, V]]) extends Map4[K1, K2, K3, K4, V] {
  def keys: Set[K1] = m.keySet.toSet;

  def keys2: Set[(K1, K2)] = map {
    case (k1, k2, k3, k4, v) => (k1, k2);
  }.toSet

  def keys3: Set[(K1, K2, K3)] = map {
    case (k1, k2, k3, k4, v) => (k1, k2, k3);
  }.toSet

  def keys4: Set[(K1, K2, K3, K4)] = map {
    case (k1, k2, k3, k4, v) => (k1, k2, k3, k4);
  }.toSet

  def getOrElse(k1: K1, k2: K2, k3: K3, k4: K4)(default: => V): V = m.get(k1) match {
    case None => default;
    case Some(m2) => m2.getOrElse(k2, k3, k4)(default);
  }

  def getOrElsePut(k1: K1, k2: K2, k3: K3, k4: K4, v: V): V = get(k1, k2, k3, k4) match {
    case None => put(k1, k2, k3, k4, v); v;
    case Some(v2) => v2;
  }

  def get(k1: K1, k2: K2, k3: K3, k4: K4): Option[V] = m.get(k1) match {
    case None => None;
    case Some(m2) => m2.get(k2, k3, k4);
  }

  def get(k1: K1, k2: K2, k3: K3): Map[K4, V] = m.get(k1) match {
    case None => immutable.Map.empty[K4, V];
    case Some(m2) => m2.get(k2, k3);
  }

  def get(k1: K1, k2: K2): Map2[K3, K4, V] = m.get(k1) match {
    case None => Map2.empty[K3, K4, V];
    case Some(m2) => m2.get(k2);
  }

  def get(k1: K1): Map3[K2, K3, K4, V] = m.get(k1) match {
    case None => Map3.empty[K2, K3, K4, V];
    case Some(m2) => m2;
  }

  def put(k1: K1, k2: K2, k3: K3, k4: K4, v: V): Unit = m.get(k1) match {
    case None => {
      val m2 = Map3.empty[K2, K3, K4, V];
      m2.put(k2, k3, k4, v);
      m.put(k1, m2);
    }
    case Some(m2) => m2.put(k2, k3, k4, v);
  }

  def remove(k1: K1, k2: K2, k3: K3, k4: K4): Unit = m.get(k1) match {
    case None => // nop
    case Some(m2) => m2.remove(k2, k3, k4);
  }

  def foreach[U](f: ((K1, K2, K3, K4, V)) => U): Unit = {
    for ((k1, m2) <- m) {
      m2 foreach {
        case (k2, k3, k4, v) => f(k1, k2, k3, k4, v);
      }
    }
  }
}

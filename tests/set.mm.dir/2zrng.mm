include "zring.mm"
include "crg.mm"
include "wcel.mm"
include "crng.mm"
include "zringring.mm"
include "2zlidl.mm"
include "lidlrng.mm"
include "mp2an.mm"

theorem 2zrng
  let vx: setvar x
  let vz: setvar z
  let cR: class R
  let cU: class U
  let cE: class E
  let va: setvar a
  let vb: setvar b
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  assume 2zrng.e: |- E = { z e. ZZ | E. x e. ZZ z = ( 2 x. x ) }
  assume 2zlidl.u: |- U = ( LIdeal ` ZZring )
  assume 2zrng.r: |- R = ( ZZring |`s E )

  disjoint x z
  disjoint x z
  disjoint a b
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint a x
  disjoint a z
  disjoint b i
  disjoint b j
  disjoint b k
  disjoint b x
  disjoint b z
  disjoint i j
  disjoint i k
  disjoint i x
  disjoint i z
  disjoint j k
  disjoint j x
  disjoint j z
  disjoint k x
  disjoint k z
  disjoint E i
  disjoint E j
  disjoint E k
  disjoint k x
  assert |- R e. Rng

  proof
    zring
    crg
    wcel
    cE
    cU
    wcel
    cR
    crng
    wcel
    zringring
    vx
    vz
    cU
    cE
    2zrng.e
    2zlidl.u
    2zlidl
    zring
    cE
    cR
    cU
    2zlidl.u
    2zrng.r
    lidlrng
    mp2an
end

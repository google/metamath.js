include "cn0.mm"
include "cvv.mm"
include "wcel.mm"
include "cword.mm"
include "wa.mm"
include "co.mm"
include "cfv.mm"
include "cv.mm"
include "crab.mm"
include "elovmpt3imp.mm"
include "wrdexg.mm"
include "adantr.mm"
include "syl.mm"
include "nn0ex.mm"
include "jctil.mm"
include "wceq.mm"
include "eqidd.mm"
include "wrdeq.mm"
include "elovmpt3rab1.mm"
include "mpcom.mm"

theorem elovmptnn0wrd
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vn: setvar n
  let cN: class N
  let cO: class O
  let cV: class V
  let cY: class Y
  let cZ: class Z
  assume elovmptnn0wrd.o: |- O = ( v e. _V , y e. _V |-> ( n e. NN0 |-> { z e. Word v | ph } ) )

  disjoint V n
  disjoint V v
  disjoint V y
  disjoint V z
  disjoint n v
  disjoint n y
  disjoint n z
  disjoint v y
  disjoint v z
  disjoint y z
  disjoint N n
  disjoint N z
  disjoint Y n
  disjoint Y v
  disjoint Y y
  disjoint Y z
  disjoint Z z
  assert |- ( Z e. ( ( V O Y ) ` N ) -> ( ( V e. _V /\ Y e. _V ) /\ ( N e. NN0 /\ Z e. Word V ) ) )

  proof
    cn0
    cvv
    wcel
    #
    cV
    cword
    #
    cvv
    wcel
    #
    wa
    cZ
    cN
    cV
    cY
    cO
    co
    cfv
    wcel
    #
    cV
    cvv
    wcel
    #
    cY
    cvv
    wcel
    #
    wa
    #
    cN
    cn0
    wcel
    cZ
    @1
    wcel
    wa
    wa
    @3
    @2
    @0
    @3
    @6
    @2
    vv
    vy
    vn
    cZ
    wph
    vz
    vv
    cv
    #
    cword
    #
    crab
    cn0
    cO
    cV
    cY
    cN
    elovmptnn0wrd.o
    elovmpt3imp
    @4
    @2
    @5
    cV
    cvv
    wrdexg
    adantr
    syl
    nn0ex
    jctil
    wph
    vv
    vy
    vn
    cZ
    cvv
    cvv
    cn0
    @1
    cn0
    @8
    cO
    cV
    cY
    cN
    vz
    elovmptnn0wrd.o
    @7
    cV
    wceq
    #
    vy
    cv
    cY
    wceq
    #
    wa
    cn0
    eqidd
    @9
    @8
    @1
    wceq
    @10
    @7
    cV
    wrdeq
    adantr
    elovmpt3rab1
    mpcom
end

include "cr.mm"
include "wcel.mm"
include "cho.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "ch0o.mm"
include "cleo.mm"
include "chot.mm"
include "co.mm"
include "wa.mm"
include "cle.mm"
include "3simpa.mm"
include "adantr.mm"
include "0re.mm"
include "ltle.mm"
include "3impia.mm"
include "mp3an1.mm"
include "3adant2.mm"
include "anim1i.mm"
include "leopmuli.mm"
include "syl2anc.mm"
include "c1.mm"
include "cdiv.mm"
include "wne.mm"
include "gt0ne0.mm"
include "rereccl.mm"
include "syldan.mm"
include "hmopm.mm"
include "3adant3.mm"
include "recgt0.mm"
include "wi.mm"
include "sylancr.mm"
include "mpd.mm"
include "jca31.mm"
include "anassrs.mm"
include "sylan.mm"
include "wceq.mm"
include "cmul.mm"
include "cc.mm"
include "recn.mm"
include "recid2d.mm"
include "oveq1d.mm"
include "chil.mm"
include "wf.mm"
include "reccld.mm"
include "3ad2ant1.mm"
include "hmopf.mm"
include "3ad2ant2.mm"
include "homulass.mm"
include "syl3anc.mm"
include "homulid2.mm"
include "syl.mm"
include "3eqtr3d.mm"
include "breqtrd.mm"
include "impbida.mm"

theorem leopmul
  let cA: class A
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let vt: setvar t
  let vu: setvar u
  let cU: class U


  assert |- ( ( A e. RR /\ T e. HrmOp /\ 0 < A ) -> ( 0hop <_op T <-> 0hop <_op ( A .op T ) ) )

  proof
    cA
    cr
    wcel
    #
    cT
    cho
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    w3a
    #
    ch0o
    cT
    cleo
    wbr
    #
    ch0o
    cA
    cT
    chot
    co
    #
    cleo
    wbr
    #
    @3
    @4
    wa
    @0
    @1
    wa
    #
    cc0
    cA
    cle
    wbr
    #
    @4
    wa
    @6
    @3
    @7
    @4
    @0
    @1
    @2
    3simpa
    adantr
    @3
    @8
    @4
    @0
    @2
    @8
    @1
    cc0
    cr
    wcel
    #
    @0
    @2
    @8
    0re
    @9
    @0
    @2
    @8
    cc0
    cA
    ltle
    3impia
    mp3an1
    3adant2
    anim1i
    cA
    cT
    leopmuli
    syl2anc
    @3
    @6
    wa
    ch0o
    c1
    cA
    cdiv
    co
    #
    @5
    chot
    co
    #
    cT
    cleo
    @3
    @10
    cr
    wcel
    #
    @5
    cho
    wcel
    #
    wa
    #
    cc0
    @10
    cle
    wbr
    #
    wa
    @6
    ch0o
    @11
    cleo
    wbr
    #
    @3
    @12
    @13
    @15
    @0
    @2
    @12
    @1
    @0
    @2
    cA
    cc0
    wne
    @12
    cA
    gt0ne0
    #
    cA
    rereccl
    syldan
    #
    3adant2
    @0
    @1
    @13
    @2
    cA
    cT
    hmopm
    3adant3
    @0
    @2
    @15
    @1
    @0
    @2
    wa
    #
    cc0
    @10
    clt
    wbr
    #
    @15
    cA
    recgt0
    @19
    @9
    @12
    @20
    @15
    wi
    0re
    @18
    cc0
    @10
    ltle
    sylancr
    mpd
    3adant2
    jca31
    @14
    @15
    @6
    @16
    @10
    @5
    leopmuli
    anassrs
    sylan
    @3
    @11
    cT
    wceq
    @6
    @3
    @10
    cA
    cmul
    co
    #
    cT
    chot
    co
    #
    c1
    cT
    chot
    co
    #
    @11
    cT
    @0
    @2
    @22
    @23
    wceq
    @1
    @19
    @21
    c1
    cT
    chot
    @19
    cA
    @0
    cA
    cc
    wcel
    #
    @2
    cA
    recn
    #
    adantr
    #
    @17
    recid2d
    oveq1d
    3adant2
    @3
    @10
    cc
    wcel
    #
    @24
    chil
    chil
    cT
    wf
    #
    @22
    @11
    wceq
    @0
    @2
    @27
    @1
    @19
    cA
    @26
    @17
    reccld
    3adant2
    @0
    @1
    @24
    @2
    @25
    3ad2ant1
    @1
    @0
    @28
    @2
    cT
    hmopf
    #
    3ad2ant2
    @10
    cA
    cT
    homulass
    syl3anc
    @1
    @0
    @23
    cT
    wceq
    #
    @2
    @1
    @28
    @30
    @29
    cT
    homulid2
    syl
    3ad2ant2
    3eqtr3d
    adantr
    breqtrd
    impbida
end

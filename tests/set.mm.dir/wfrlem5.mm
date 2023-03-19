include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "cdm.mm"
include "cin.mm"
include "cres.mm"
include "wcel.mm"
include "wceq.mm"
include "vex.mm"
include "breldm.mm"
include "anim12i.mm"
include "elin.mm"
include "sylibr.mm"
include "anandir.mm"
include "brres.mm"
include "anbi12i.mm"
include "sylbb2.mm"
include "mpdan.mm"
include "wwe.mm"
include "wse.mm"
include "wfn.mm"
include "cfv.mm"
include "cpred.mm"
include "wral.mm"
include "wss.mm"
include "wfrlem3.mm"
include "ssinss1.mm"
include "wess.mm"
include "mpi.mm"
include "sess2.mm"
include "jca.mm"
include "3syl.mm"
include "adantr.mm"
include "wfrlem4.mm"
include "ancoms.mm"
include "incom.mm"
include "reseq2i.mm"
include "fneq1i.mm"
include "fneq2i.mm"
include "bitri.mm"
include "fveq1i.mm"
include "predeq2.mm"
include "ax-mp.mm"
include "reseq12i.mm"
include "fveq2i.mm"
include "eqeq12i.mm"
include "raleqbii.mm"
include "wfr3g.mm"
include "syl3anc.mm"
include "breqd.mm"
include "biimprd.mm"
include "wi.mm"
include "wfun.mm"
include "wal.mm"
include "wfrlem2.mm"
include "funres.mm"
include "wrel.mm"
include "dffun2.mm"
include "simprbi.mm"
include "2sp.mm"
include "sps.mm"
include "4syl.mm"
include "sylan2d.mm"
include "syl5.mm"

theorem wfrlem5
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cF: class F
  let va: setvar a
  assume wfrlem5.1: |- R We A
  assume wfrlem5.2: |- R Se A
  assume wfrlem5.3: |- B = { f | E. x ( f Fn x /\ ( x C_ A /\ A. y e. x Pred ( R , A , y ) C_ x ) /\ A. y e. x ( f ` y ) = ( F ` ( f |` Pred ( R , A , y ) ) ) ) }

  disjoint A f
  disjoint A g
  disjoint A h
  disjoint A x
  disjoint A y
  disjoint f g
  disjoint f h
  disjoint f x
  disjoint f y
  disjoint g h
  disjoint g x
  disjoint g y
  disjoint h x
  disjoint h y
  disjoint x y
  disjoint F f
  disjoint F g
  disjoint F h
  disjoint F x
  disjoint F y
  disjoint R f
  disjoint R g
  disjoint R h
  disjoint R x
  disjoint R y
  disjoint g u
  disjoint g v
  disjoint h u
  disjoint h v
  disjoint u v
  disjoint u x
  disjoint v x
  disjoint A a
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a x
  disjoint a y
  disjoint B a
  disjoint F a
  disjoint R a
  assert |- ( ( g e. B /\ h e. B ) -> ( ( x g u /\ x h v ) -> u = v ) )

  proof
    vx
    cv
    #
    vu
    cv
    #
    vg
    cv
    #
    wbr
    #
    @0
    vv
    cv
    #
    vh
    cv
    #
    wbr
    #
    wa
    #
    @0
    @1
    @2
    @2
    cdm
    #
    @5
    cdm
    #
    cin
    #
    cres
    #
    wbr
    #
    @0
    @4
    @5
    @10
    cres
    #
    wbr
    #
    wa
    #
    @2
    cB
    wcel
    #
    @5
    cB
    wcel
    #
    wa
    #
    @1
    @4
    wceq
    #
    @7
    @0
    @10
    wcel
    #
    @15
    @7
    @0
    @8
    wcel
    #
    @0
    @9
    wcel
    #
    wa
    @20
    @3
    @21
    @6
    @22
    @0
    @1
    @2
    vx
    vex
    #
    vu
    vex
    #
    breldm
    @0
    @4
    @5
    @23
    vv
    vex
    #
    breldm
    anim12i
    @0
    @8
    @9
    elin
    sylibr
    @7
    @20
    wa
    @3
    @20
    wa
    #
    @6
    @20
    wa
    #
    wa
    @15
    @3
    @6
    @20
    anandir
    @12
    @26
    @14
    @27
    @0
    @1
    @2
    @10
    @24
    brres
    @0
    @4
    @5
    @10
    @25
    brres
    anbi12i
    sylbb2
    mpdan
    @18
    @14
    @0
    @4
    @11
    wbr
    #
    @12
    @19
    @18
    @28
    @14
    @18
    @11
    @13
    @0
    @4
    @18
    @10
    cR
    wwe
    #
    @10
    cR
    wse
    #
    wa
    #
    @11
    @10
    wfn
    va
    cv
    #
    @11
    cfv
    @11
    @10
    cR
    @32
    cpred
    #
    cres
    cF
    cfv
    wceq
    va
    @10
    wral
    wa
    @13
    @10
    wfn
    #
    @32
    @13
    cfv
    #
    @13
    @33
    cres
    #
    cF
    cfv
    #
    wceq
    #
    va
    @10
    wral
    #
    wa
    #
    @11
    @13
    wceq
    @16
    @31
    @17
    @16
    @8
    cA
    wss
    @10
    cA
    wss
    #
    @31
    vx
    vy
    cA
    cB
    cR
    vf
    vg
    cF
    wfrlem5.3
    wfrlem3
    @8
    @9
    cA
    ssinss1
    @41
    @29
    @30
    @41
    cA
    cR
    wwe
    @29
    wfrlem5.1
    @10
    cA
    cR
    wess
    mpi
    @41
    cA
    cR
    wse
    @30
    wfrlem5.2
    @10
    cA
    cR
    sess2
    mpi
    jca
    3syl
    adantr
    vx
    vy
    cA
    cB
    cR
    vf
    vg
    vh
    cF
    va
    wfrlem5.1
    wfrlem5.3
    wfrlem4
    @18
    @5
    @9
    @8
    cin
    #
    cres
    #
    @42
    wfn
    #
    @32
    @43
    cfv
    #
    @43
    @42
    cR
    @32
    cpred
    #
    cres
    #
    cF
    cfv
    #
    wceq
    #
    va
    @42
    wral
    #
    wa
    #
    @40
    @17
    @16
    @51
    vx
    vy
    cA
    cB
    cR
    vf
    vh
    vg
    cF
    va
    wfrlem5.1
    wfrlem5.3
    wfrlem4
    ancoms
    @34
    @44
    @39
    @50
    @34
    @43
    @10
    wfn
    @44
    @10
    @13
    @43
    @10
    @42
    @5
    @8
    @9
    incom
    #
    reseq2i
    #
    fneq1i
    @10
    @42
    @43
    @52
    fneq2i
    bitri
    @38
    @49
    va
    @10
    @42
    @52
    @35
    @45
    @37
    @48
    @32
    @13
    @43
    @53
    fveq1i
    @36
    @47
    cF
    @13
    @43
    @33
    @46
    @53
    @10
    @42
    wceq
    @33
    @46
    wceq
    @52
    @10
    @42
    cR
    @32
    predeq2
    ax-mp
    reseq12i
    fveq2i
    eqeq12i
    raleqbii
    anbi12i
    sylibr
    va
    @10
    cR
    @11
    @13
    cF
    wfr3g
    syl3anc
    breqd
    biimprd
    @16
    @12
    @28
    wa
    @19
    wi
    #
    @17
    @16
    @2
    wfun
    @11
    wfun
    #
    @54
    vv
    wal
    vu
    wal
    #
    vx
    wal
    #
    @54
    vx
    vy
    cA
    cB
    cR
    vf
    vg
    cF
    wfrlem5.3
    wfrlem2
    @10
    @2
    funres
    @55
    @11
    wrel
    @57
    vx
    vu
    vv
    @11
    dffun2
    simprbi
    @56
    @54
    vx
    @54
    vu
    vv
    2sp
    sps
    4syl
    adantr
    sylan2d
    syl5
end

include "cipo.mm"
include "cfv.mm"
include "cdrs.mm"
include "wcel.mm"
include "cvv.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cun.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "w3a.mm"
include "cbs.mm"
include "wceq.mm"
include "eqid.mm"
include "drsbn0.mm"
include "neneqd.mm"
include "wn.mm"
include "fvprc.mm"
include "fveq2d.mm"
include "base0.mm"
include "syl6eqr.mm"
include "nsyl2.mm"
include "simp1.mm"
include "cpreset.mm"
include "cple.mm"
include "wbr.mm"
include "wa.mm"
include "isdrs.mm"
include "cpo.mm"
include "ipopos.mm"
include "posprs.mm"
include "mp1i.mm"
include "id.mm"
include "2thd.mm"
include "wb.mm"
include "ipobas.mm"
include "neeq1.mm"
include "rexeq.mm"
include "raleqbi1dv.mm"
include "anbi12d.mm"
include "syl.mm"
include "simpll.mm"
include "simplrl.mm"
include "simpr.mm"
include "ipole.mm"
include "syl3anc.mm"
include "simplrr.mm"
include "unss.mm"
include "syl6bb.mm"
include "rexbidva.mm"
include "2ralbidva.mm"
include "anbi2d.mm"
include "bitr3d.mm"
include "3anass.mm"
include "3bitr4g.mm"
include "syl5bb.mm"
include "pm5.21nii.mm"

theorem isipodrs
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vw: setvar w
  let cX: class X

  disjoint A z
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A w
  disjoint w z
  disjoint X w
  disjoint X z
  assert |- ( ( toInc ` A ) e. Dirset <-> ( A e. _V /\ A =/= (/) /\ A. x e. A A. y e. A E. z e. A ( x u. y ) C_ z ) )

  proof
    cA
    cipo
    cfv
    #
    cdrs
    wcel
    #
    cA
    cvv
    wcel
    #
    @2
    cA
    c0
    wne
    #
    vx
    cv
    #
    vy
    cv
    #
    cun
    vz
    cv
    #
    wss
    #
    vz
    cA
    wrex
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    w3a
    #
    @1
    @0
    cbs
    cfv
    #
    c0
    wceq
    @2
    @1
    @11
    c0
    @11
    @0
    @11
    eqid
    #
    drsbn0
    neneqd
    @2
    wn
    #
    @11
    c0
    cbs
    cfv
    c0
    @13
    @0
    c0
    cbs
    cA
    cipo
    fvprc
    fveq2d
    base0
    syl6eqr
    nsyl2
    @2
    @3
    @9
    simp1
    @1
    @0
    cpreset
    wcel
    #
    @11
    c0
    wne
    #
    @4
    @6
    @0
    cple
    cfv
    #
    wbr
    #
    @5
    @6
    @16
    wbr
    #
    wa
    #
    vz
    @11
    wrex
    #
    vy
    @11
    wral
    #
    vx
    @11
    wral
    #
    w3a
    #
    @2
    @10
    vx
    vy
    vz
    @11
    @0
    @16
    @12
    @16
    eqid
    #
    isdrs
    @2
    @14
    @15
    @22
    wa
    #
    wa
    @2
    @3
    @9
    wa
    #
    wa
    @23
    @10
    @2
    @14
    @2
    @25
    @26
    @2
    @14
    @2
    @0
    cpo
    wcel
    @14
    @2
    cA
    @0
    @0
    eqid
    #
    ipopos
    @0
    posprs
    mp1i
    @2
    id
    2thd
    @2
    @3
    @19
    vz
    cA
    wrex
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    wa
    #
    @25
    @26
    @2
    cA
    @11
    wceq
    #
    @31
    @25
    wb
    cA
    @0
    cvv
    @27
    ipobas
    @32
    @3
    @15
    @30
    @22
    cA
    @11
    c0
    neeq1
    @29
    @21
    vx
    cA
    @11
    @28
    @20
    vy
    cA
    @11
    @19
    vz
    cA
    @11
    rexeq
    raleqbi1dv
    raleqbi1dv
    anbi12d
    syl
    @2
    @30
    @9
    @3
    @2
    @28
    @8
    vx
    vy
    cA
    cA
    @2
    @4
    cA
    wcel
    #
    @5
    cA
    wcel
    #
    wa
    #
    wa
    #
    @19
    @7
    vz
    cA
    @36
    @6
    cA
    wcel
    #
    wa
    #
    @19
    @4
    @6
    wss
    #
    @5
    @6
    wss
    #
    wa
    @7
    @38
    @17
    @39
    @18
    @40
    @38
    @2
    @33
    @37
    @17
    @39
    wb
    @2
    @35
    @37
    simpll
    #
    @2
    @33
    @34
    @37
    simplrl
    @36
    @37
    simpr
    #
    cA
    @0
    @16
    cvv
    @4
    @6
    @27
    @24
    ipole
    syl3anc
    @38
    @2
    @34
    @37
    @18
    @40
    wb
    @41
    @2
    @33
    @34
    @37
    simplrr
    @42
    cA
    @0
    @16
    cvv
    @5
    @6
    @27
    @24
    ipole
    syl3anc
    anbi12d
    @4
    @5
    @6
    unss
    syl6bb
    rexbidva
    2ralbidva
    anbi2d
    bitr3d
    anbi12d
    @14
    @15
    @22
    3anass
    @2
    @3
    @9
    3anass
    3bitr4g
    syl5bb
    pm5.21nii
end

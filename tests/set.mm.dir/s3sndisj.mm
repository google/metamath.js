include "wcel.mm"
include "wa.mm"
include "weq.mm"
include "cv.mm"
include "cs3.mm"
include "csn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "wral.mm"
include "wdisj.mm"
include "wi.mm"
include "orc.mm"
include "a1d.mm"
include "wn.mm"
include "wne.mm"
include "chash.mm"
include "cfv.mm"
include "c3.mm"
include "cc0.mm"
include "c1.mm"
include "c2.mm"
include "w3a.mm"
include "cvv.mm"
include "cword.mm"
include "wb.mm"
include "s3cli.mm"
include "elex.mm"
include "anim12i.mm"
include "adantl.mm"
include "df-3an.mm"
include "sylibr.mm"
include "eqwrds3.mm"
include "sylancr.mm"
include "vex.mm"
include "s3fv2.mm"
include "ax-mp.mm"
include "simp3.mm"
include "syl5eqr.mm"
include "syl6bi.mm"
include "con3rr3.mm"
include "imp.mm"
include "neqned.mm"
include "disjsn2.mm"
include "syl.mm"
include "olcd.mm"
include "ex.mm"
include "pm2.61i.mm"
include "ralrimivva.mm"
include "eqidd.mm"
include "id.mm"
include "s3eqd.mm"
include "sneqd.mm"
include "disjor.mm"

theorem s3sndisj
  let cA: class A
  let cB: class B
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vc: setvar c
  let vd: setvar d

  disjoint A c
  disjoint B c
  disjoint X c
  disjoint Y c
  disjoint Z c
  disjoint A d
  disjoint c d
  disjoint B d
  disjoint X d
  disjoint Y d
  disjoint Z d
  assert |- ( ( A e. X /\ B e. Y ) -> Disj_ c e. Z { <" A B c "> } )

  proof
    cA
    cX
    wcel
    #
    cB
    cY
    wcel
    #
    wa
    #
    vc
    vd
    weq
    #
    cA
    cB
    vc
    cv
    #
    cs3
    #
    csn
    #
    cA
    cB
    vd
    cv
    #
    cs3
    #
    csn
    #
    cin
    c0
    wceq
    #
    wo
    #
    vd
    cZ
    wral
    vc
    cZ
    wral
    vc
    cZ
    @6
    wdisj
    @2
    @11
    vc
    vd
    cZ
    cZ
    @3
    @2
    @4
    cZ
    wcel
    #
    @7
    cZ
    wcel
    #
    wa
    #
    wa
    #
    @11
    wi
    @3
    @11
    @15
    @3
    @10
    orc
    a1d
    @3
    wn
    #
    @15
    @11
    @16
    @15
    wa
    #
    @10
    @3
    @17
    @5
    @8
    wne
    @10
    @17
    @5
    @8
    @16
    @15
    @5
    @8
    wceq
    #
    wn
    @15
    @18
    @3
    @15
    @18
    @5
    chash
    cfv
    c3
    wceq
    #
    cc0
    @5
    cfv
    cA
    wceq
    #
    c1
    @5
    cfv
    cB
    wceq
    #
    c2
    @5
    cfv
    #
    @7
    wceq
    #
    w3a
    #
    wa
    #
    @3
    @15
    @5
    cvv
    cword
    wcel
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    @7
    cvv
    wcel
    #
    w3a
    #
    @18
    @25
    wb
    cA
    cB
    @4
    s3cli
    @15
    @26
    @27
    wa
    #
    @28
    wa
    @29
    @2
    @30
    @14
    @28
    @0
    @26
    @1
    @27
    cA
    cX
    elex
    cB
    cY
    elex
    anim12i
    @13
    @28
    @12
    @7
    cZ
    elex
    adantl
    anim12i
    @26
    @27
    @28
    df-3an
    sylibr
    cA
    cB
    @7
    cvv
    @5
    eqwrds3
    sylancr
    @24
    @3
    @19
    @24
    @4
    @22
    @7
    @4
    cvv
    wcel
    @22
    @4
    wceq
    vc
    vex
    cA
    cB
    @4
    cvv
    s3fv2
    ax-mp
    @20
    @21
    @23
    simp3
    syl5eqr
    adantl
    syl6bi
    con3rr3
    imp
    neqned
    @5
    @8
    disjsn2
    syl
    olcd
    ex
    pm2.61i
    ralrimivva
    cZ
    @6
    @9
    vc
    vd
    @3
    @5
    @8
    @3
    cA
    cB
    @4
    @7
    cA
    cB
    @3
    cA
    eqidd
    @3
    cB
    eqidd
    @3
    id
    s3eqd
    sneqd
    disjor
    sylibr
end

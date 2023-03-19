include "cs3.mm"
include "ceqlg.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "c1.mm"
include "c2.mm"
include "cc0.mm"
include "ccgrg.mm"
include "wbr.mm"
include "c3.mm"
include "cfzo.mm"
include "co.mm"
include "cmap.mm"
include "crab.mm"
include "wa.mm"
include "cstrkg.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "cbs.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveq1d.mm"
include "breqd.mm"
include "rabeqbidv.mm"
include "df-eqlg.mm"
include "ovex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "3syl.mm"
include "eleq2d.mm"
include "wb.mm"
include "id.mm"
include "fveq1.mm"
include "s3eqd.mm"
include "breq12d.mm"
include "elrab.mm"
include "a1i.mm"
include "cword.mm"
include "chash.mm"
include "s3cld.mm"
include "s3len.mm"
include "jca.mm"
include "cn0.mm"
include "fvex.mm"
include "eqeltri.mm"
include "3nn0.mm"
include "wrdmap.mm"
include "mp2an.mm"
include "sylib.mm"
include "biantrurd.mm"
include "s3fv1.mm"
include "syl.mm"
include "s3fv2.mm"
include "s3fv0.mm"
include "breq2d.mm"
include "bitr3d.mm"
include "3bitrd.mm"

theorem iseqlg
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let vx: setvar x
  let vg: setvar g
  assume iseqlg.p: |- P = ( Base ` G )
  assume iseqlg.m: |- .- = ( dist ` G )
  assume iseqlg.i: |- I = ( Itv ` G )
  assume iseqlg.l: |- L = ( LineG ` G )
  assume iseqlg.g: |- ( ph -> G e. TarskiG )
  assume iseqlg.a: |- ( ph -> A e. P )
  assume iseqlg.b: |- ( ph -> B e. P )
  assume iseqlg.c: |- ( ph -> C e. P )


  assert |- ( ph -> ( <" A B C "> e. ( eqltrG ` G ) <-> <" A B C "> ( cgrG ` G ) <" B C A "> ) )

  proof
    wph
    cA
    cB
    cC
    cs3
    #
    cG
    ceqlg
    cfv
    #
    wcel
    @0
    vx
    cv
    #
    c1
    @2
    cfv
    #
    c2
    @2
    cfv
    #
    cc0
    @2
    cfv
    #
    cs3
    #
    cG
    ccgrg
    cfv
    #
    wbr
    #
    vx
    cP
    cc0
    c3
    cfzo
    co
    #
    cmap
    co
    #
    crab
    #
    wcel
    #
    @0
    @10
    wcel
    #
    @0
    c1
    @0
    cfv
    #
    c2
    @0
    cfv
    #
    cc0
    @0
    cfv
    #
    cs3
    #
    @7
    wbr
    #
    wa
    #
    @0
    cB
    cC
    cA
    cs3
    #
    @7
    wbr
    #
    wph
    @1
    @11
    @0
    wph
    cG
    cstrkg
    wcel
    cG
    cvv
    wcel
    @1
    @11
    wceq
    iseqlg.g
    cG
    cstrkg
    elex
    vg
    cG
    @2
    @6
    vg
    cv
    #
    ccgrg
    cfv
    #
    wbr
    #
    vx
    @22
    cbs
    cfv
    #
    @9
    cmap
    co
    #
    crab
    @11
    cvv
    ceqlg
    @22
    cG
    wceq
    #
    @24
    @8
    vx
    @26
    @10
    @27
    @25
    cP
    @9
    cmap
    @27
    @25
    cG
    cbs
    cfv
    #
    cP
    @22
    cG
    cbs
    fveq2
    iseqlg.p
    syl6eqr
    oveq1d
    @27
    @23
    @7
    @2
    @6
    @22
    cG
    ccgrg
    fveq2
    breqd
    rabeqbidv
    vx
    vg
    df-eqlg
    @8
    vx
    @10
    cP
    @9
    cmap
    ovex
    rabex
    fvmpt
    3syl
    eleq2d
    @12
    @19
    wb
    wph
    @8
    @18
    vx
    @0
    @10
    @2
    @0
    wceq
    #
    @2
    @0
    @6
    @17
    @7
    @29
    id
    @29
    @3
    @4
    @5
    @16
    @14
    @15
    c1
    @2
    @0
    fveq1
    c2
    @2
    @0
    fveq1
    cc0
    @2
    @0
    fveq1
    s3eqd
    breq12d
    elrab
    a1i
    wph
    @18
    @19
    @21
    wph
    @13
    @18
    wph
    @0
    cP
    cword
    wcel
    #
    @0
    chash
    cfv
    c3
    wceq
    #
    wa
    #
    @13
    wph
    @30
    @31
    wph
    cA
    cB
    cC
    cP
    iseqlg.a
    iseqlg.b
    iseqlg.c
    s3cld
    @31
    wph
    cA
    cB
    cC
    s3len
    a1i
    jca
    cP
    cvv
    wcel
    c3
    cn0
    wcel
    @32
    @13
    wb
    cP
    @28
    cvv
    iseqlg.p
    cG
    cbs
    fvex
    eqeltri
    3nn0
    c3
    cP
    @0
    cvv
    wrdmap
    mp2an
    sylib
    biantrurd
    wph
    @17
    @20
    @0
    @7
    wph
    @14
    @15
    @16
    cA
    cB
    cC
    wph
    cB
    cP
    wcel
    @14
    cB
    wceq
    iseqlg.b
    cA
    cB
    cC
    cP
    s3fv1
    syl
    wph
    cC
    cP
    wcel
    @15
    cC
    wceq
    iseqlg.c
    cA
    cB
    cC
    cP
    s3fv2
    syl
    wph
    cA
    cP
    wcel
    @16
    cA
    wceq
    iseqlg.a
    cA
    cB
    cC
    cP
    s3fv0
    syl
    s3eqd
    breq2d
    bitr3d
    3bitrd
end

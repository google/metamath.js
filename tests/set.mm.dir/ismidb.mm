include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "crio.mm"
include "cmid.mm"
include "co.mm"
include "wcel.mm"
include "wreu.mm"
include "wb.mm"
include "clng.mm"
include "eqid.mm"
include "mideu.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "eqeq2d.mm"
include "riota2.mm"
include "syl2anc.mm"
include "cbs.mm"
include "cmir.mm"
include "cmpt2.mm"
include "cvv.mm"
include "cmpt.mm"
include "df-mid.mm"
include "a1i.mm"
include "syl6eqr.mm"
include "riotaeqbidv.mm"
include "mpt2eq123dv.mm"
include "adantl.mm"
include "cstrkg.mm"
include "elex.mm"
include "syl.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "fvmptd.mm"
include "wa.mm"
include "simprr.mm"
include "simprl.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "riotabidv.mm"
include "riotacl.mm"
include "ovmpt2d.mm"
include "eqeq1d.mm"
include "bitr4d.mm"

theorem ismidb
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cS: class S
  let cG: class G
  let cI: class I
  let cM: class M
  let c.mi: class .-
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vg: setvar g
  let cL: class L
  assume ismid.p: |- P = ( Base ` G )
  assume ismid.d: |- .- = ( dist ` G )
  assume ismid.i: |- I = ( Itv ` G )
  assume ismid.g: |- ( ph -> G e. TarskiG )
  assume ismid.1: |- ( ph -> G TarskiGDim>= 2 )
  assume midcl.1: |- ( ph -> A e. P )
  assume midcl.2: |- ( ph -> B e. P )
  assume ismidb.s: |- S = ( pInvG ` G )
  assume ismidb.m: |- ( ph -> M e. P )


  assert |- ( ph -> ( B = ( ( S ` M ) ` A ) <-> ( A ( midG ` G ) B ) = M ) )

  proof
    wph
    cB
    cA
    cM
    cS
    cfv
    #
    cfv
    #
    wceq
    #
    cB
    cA
    vm
    cv
    #
    cS
    cfv
    #
    cfv
    #
    wceq
    #
    vm
    cP
    crio
    #
    cM
    wceq
    #
    cA
    cB
    cG
    cmid
    cfv
    #
    co
    #
    cM
    wceq
    wph
    cM
    cP
    wcel
    @6
    vm
    cP
    wreu
    #
    @2
    @8
    wb
    ismidb.m
    wph
    vm
    cA
    cB
    cP
    cS
    cG
    cI
    cG
    clng
    cfv
    #
    c.mi
    ismid.p
    ismid.d
    ismid.i
    @12
    eqid
    ismid.g
    ismidb.s
    midcl.1
    midcl.2
    ismid.1
    mideu
    #
    @6
    @2
    vm
    cP
    cM
    @3
    cM
    wceq
    #
    @5
    @1
    cB
    @14
    cA
    @4
    @0
    @3
    cM
    cS
    fveq2
    fveq1d
    eqeq2d
    riota2
    syl2anc
    wph
    @10
    @7
    cM
    wph
    va
    vb
    cA
    cB
    cP
    cP
    vb
    cv
    #
    va
    cv
    #
    @4
    cfv
    #
    wceq
    #
    vm
    cP
    crio
    #
    @7
    @9
    cP
    wph
    vg
    cG
    va
    vb
    vg
    cv
    #
    cbs
    cfv
    #
    @21
    @15
    @16
    @3
    @20
    cmir
    cfv
    #
    cfv
    #
    cfv
    #
    wceq
    #
    vm
    @21
    crio
    #
    cmpt2
    #
    va
    vb
    cP
    cP
    @19
    cmpt2
    #
    cvv
    cmid
    cvv
    cmid
    vg
    cvv
    @27
    cmpt
    wceq
    wph
    vg
    vm
    va
    vb
    df-mid
    a1i
    @20
    cG
    wceq
    #
    @27
    @28
    wceq
    wph
    @29
    va
    vb
    @21
    @21
    @26
    cP
    cP
    @19
    @29
    @21
    cG
    cbs
    cfv
    #
    cP
    @20
    cG
    cbs
    fveq2
    ismid.p
    syl6eqr
    #
    @31
    @29
    @25
    @18
    vm
    @21
    cP
    @31
    @29
    @24
    @17
    @15
    @29
    @16
    @23
    @4
    @29
    @3
    @22
    cS
    @29
    @22
    cG
    cmir
    cfv
    cS
    @20
    cG
    cmir
    fveq2
    ismidb.s
    syl6eqr
    fveq1d
    fveq1d
    eqeq2d
    riotaeqbidv
    mpt2eq123dv
    adantl
    wph
    cG
    cstrkg
    wcel
    cG
    cvv
    wcel
    ismid.g
    cG
    cstrkg
    elex
    syl
    @28
    cvv
    wcel
    wph
    va
    vb
    cP
    cP
    @19
    cP
    @30
    cvv
    ismid.p
    cG
    cbs
    fvex
    eqeltri
    #
    @32
    mpt2ex
    a1i
    fvmptd
    wph
    @16
    cA
    wceq
    #
    @15
    cB
    wceq
    #
    wa
    wa
    #
    @18
    @6
    vm
    cP
    @35
    @15
    cB
    @17
    @5
    wph
    @33
    @34
    simprr
    @35
    @16
    cA
    @4
    wph
    @33
    @34
    simprl
    fveq2d
    eqeq12d
    riotabidv
    midcl.1
    midcl.2
    wph
    @11
    @7
    cP
    wcel
    @13
    @6
    vm
    cP
    riotacl
    syl
    ovmpt2d
    eqeq1d
    bitr4d
end

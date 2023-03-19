include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "crest.mm"
include "co.mm"
include "cfil.mm"
include "ccl.mm"
include "wcel.mm"
include "cdif.mm"
include "clp.mm"
include "ctop.mm"
include "cc.mm"
include "wss.mm"
include "wb.mm"
include "cnfldtop.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "islp.mm"
include "sylancr.mm"
include "mpbid.mm"
include "fveq2i.mm"
include "syl6eleqr.mm"
include "ctopon.mm"
include "a1i.mm"
include "difss.mm"
include "eqsstri.mm"
include "syl5ss.mm"
include "lpss.mm"
include "sseldd.mm"
include "trnei.mm"
include "syl3anc.mm"
include "syl5eqel.mm"

theorem limcflflem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cK: class K
  let cL: class L
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  assume limcflf.f: |- ( ph -> F : A --> CC )
  assume limcflf.a: |- ( ph -> A C_ CC )
  assume limcflf.b: |- ( ph -> B e. ( ( limPt ` K ) ` A ) )
  assume limcflf.k: |- K = ( TopOpen ` CCfld )
  assume limcflf.c: |- C = ( A \ { B } )
  assume limcflf.l: |- L = ( ( ( nei ` K ) ` { B } ) |`t C )


  assert |- ( ph -> L e. ( Fil ` C ) )

  proof
    wph
    cL
    cB
    csn
    #
    cK
    cnei
    cfv
    cfv
    cC
    crest
    co
    #
    cC
    cfil
    cfv
    #
    limcflf.l
    wph
    cB
    cC
    cK
    ccl
    cfv
    #
    cfv
    #
    wcel
    #
    @1
    @2
    wcel
    #
    wph
    cB
    cA
    @0
    cdif
    #
    @3
    cfv
    #
    @4
    wph
    cB
    cA
    cK
    clp
    cfv
    cfv
    #
    wcel
    #
    cB
    @8
    wcel
    #
    limcflf.b
    wph
    cK
    ctop
    wcel
    #
    cA
    cc
    wss
    #
    @10
    @11
    wb
    cK
    limcflf.k
    cnfldtop
    #
    limcflf.a
    cB
    cA
    cK
    cc
    cc
    cK
    cK
    limcflf.k
    cnfldtopon
    #
    toponunii
    #
    islp
    sylancr
    mpbid
    cC
    @7
    @3
    limcflf.c
    fveq2i
    syl6eleqr
    wph
    cK
    cc
    ctopon
    cfv
    wcel
    #
    cC
    cc
    wss
    cB
    cc
    wcel
    @5
    @6
    wb
    @17
    wph
    @15
    a1i
    wph
    cC
    cA
    cc
    cC
    @7
    cA
    limcflf.c
    cA
    @0
    difss
    eqsstri
    limcflf.a
    syl5ss
    wph
    @9
    cc
    cB
    wph
    @12
    @13
    @9
    cc
    wss
    @14
    limcflf.a
    cA
    cK
    cc
    @16
    lpss
    sylancr
    limcflf.b
    sseldd
    cC
    cB
    cK
    cc
    trnei
    syl3anc
    mpbid
    syl5eqel
end

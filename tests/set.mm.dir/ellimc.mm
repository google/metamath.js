include "climc.mm"
include "co.mm"
include "wcel.mm"
include "csn.mm"
include "cun.mm"
include "cv.mm"
include "wceq.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt.mm"
include "ccnp.mm"
include "cab.mm"
include "cc.mm"
include "wss.mm"
include "wf.mm"
include "wa.mm"
include "limcfval.mm"
include "syl3anc.mm"
include "simpld.mm"
include "eleq2d.mm"
include "wi.mm"
include "wb.mm"
include "limcvallem.mm"
include "ifeq1.mm"
include "mpteq2dv.mm"
include "syl6eqr.mm"
include "eleq1d.mm"
include "elab3g.mm"
include "syl.mm"
include "bitrd.mm"

theorem ellimc
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let vf: setvar f
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  assume limcval.j: |- J = ( K |`t ( A u. { B } ) )
  assume limcval.k: |- K = ( TopOpen ` CCfld )
  assume ellimc.g: |- G = ( z e. ( A u. { B } ) |-> if ( z = B , C , ( F ` z ) ) )
  assume ellimc.f: |- ( ph -> F : A --> CC )
  assume ellimc.a: |- ( ph -> A C_ CC )
  assume ellimc.b: |- ( ph -> B e. CC )

  disjoint A z
  disjoint B z
  disjoint F z
  disjoint K z
  disjoint C z
  disjoint f j
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint A j
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint B f
  disjoint B j
  disjoint B x
  disjoint B y
  disjoint F f
  disjoint F j
  disjoint F x
  disjoint F y
  disjoint K f
  disjoint K j
  disjoint K x
  disjoint K y
  disjoint C y
  disjoint G y
  disjoint J f
  disjoint J j
  disjoint J x
  disjoint J y
  assert |- ( ph -> ( C e. ( F limCC B ) <-> G e. ( ( J CnP K ) ` B ) ) )

  proof
    wph
    cC
    cF
    cB
    climc
    co
    #
    wcel
    cC
    vz
    cA
    cB
    csn
    cun
    #
    vz
    cv
    #
    cB
    wceq
    #
    vy
    cv
    #
    @2
    cF
    cfv
    #
    cif
    #
    cmpt
    #
    cB
    cJ
    cK
    ccnp
    co
    cfv
    #
    wcel
    #
    vy
    cab
    #
    wcel
    #
    cG
    @8
    wcel
    #
    wph
    @0
    @10
    cC
    wph
    @0
    @10
    wceq
    #
    @0
    cc
    wss
    #
    wph
    cA
    cc
    cF
    wf
    #
    cA
    cc
    wss
    #
    cB
    cc
    wcel
    #
    @13
    @14
    wa
    ellimc.f
    ellimc.a
    ellimc.b
    vy
    vz
    cA
    cB
    cF
    cJ
    cK
    limcval.j
    limcval.k
    limcfval
    syl3anc
    simpld
    eleq2d
    wph
    @12
    cC
    cc
    wcel
    wi
    #
    @11
    @12
    wb
    wph
    @15
    @16
    @17
    @18
    ellimc.f
    ellimc.a
    ellimc.b
    vz
    cA
    cB
    cC
    cF
    cG
    cJ
    cK
    limcval.j
    limcval.k
    ellimc.g
    limcvallem
    syl3anc
    @9
    @12
    vy
    cC
    cc
    @4
    cC
    wceq
    #
    @7
    cG
    @8
    @19
    @7
    vz
    @1
    @3
    cC
    @5
    cif
    #
    cmpt
    cG
    @19
    vz
    @1
    @6
    @20
    @3
    @4
    cC
    @5
    ifeq1
    mpteq2dv
    ellimc.g
    syl6eqr
    eleq1d
    elab3g
    syl
    bitrd
end

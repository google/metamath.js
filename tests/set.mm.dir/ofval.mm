include "wcel.mm"
include "wa.mm"
include "cof.mm"
include "co.mm"
include "cfv.mm"
include "cv.mm"
include "cmpt.mm"
include "wceq.mm"
include "eqidd.mm"
include "offval.mm"
include "fveq1d.mm"
include "adantr.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "cin.mm"
include "inss1.mm"
include "eqsstr3i.mm"
include "sseli.mm"
include "sylan2.mm"
include "inss2.mm"
include "3eqtrd.mm"

theorem ofval
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  assume offval.1: |- ( ph -> F Fn A )
  assume offval.2: |- ( ph -> G Fn B )
  assume offval.3: |- ( ph -> A e. V )
  assume offval.4: |- ( ph -> B e. W )
  assume offval.5: |- ( A i^i B ) = S
  assume ofval.6: |- ( ( ph /\ X e. A ) -> ( F ` X ) = C )
  assume ofval.7: |- ( ( ph /\ X e. B ) -> ( G ` X ) = D )


  assert |- ( ( ph /\ X e. S ) -> ( ( F oF R G ) ` X ) = ( C R D ) )

  proof
    wph
    cX
    cS
    wcel
    #
    wa
    #
    cX
    cF
    cG
    cR
    cof
    co
    #
    cfv
    #
    cX
    vx
    cS
    vx
    cv
    #
    cF
    cfv
    #
    @4
    cG
    cfv
    #
    cR
    co
    #
    cmpt
    #
    cfv
    #
    cX
    cF
    cfv
    #
    cX
    cG
    cfv
    #
    cR
    co
    #
    cC
    cD
    cR
    co
    wph
    @3
    @9
    wceq
    @0
    wph
    cX
    @2
    @8
    wph
    vx
    cA
    cB
    @5
    @6
    cR
    cS
    cF
    cG
    cV
    cW
    offval.1
    offval.2
    offval.3
    offval.4
    offval.5
    wph
    @4
    cA
    wcel
    wa
    @5
    eqidd
    wph
    @4
    cB
    wcel
    wa
    @6
    eqidd
    offval
    fveq1d
    adantr
    @0
    @9
    @12
    wceq
    wph
    vx
    cX
    @7
    @12
    cS
    @8
    @4
    cX
    wceq
    @5
    @10
    @6
    @11
    cR
    @4
    cX
    cF
    fveq2
    @4
    cX
    cG
    fveq2
    oveq12d
    @8
    eqid
    @10
    @11
    cR
    ovex
    fvmpt
    adantl
    @1
    @10
    cC
    @11
    cD
    cR
    @0
    wph
    cX
    cA
    wcel
    @10
    cC
    wceq
    cS
    cA
    cX
    cS
    cA
    cB
    cin
    #
    cA
    offval.5
    cA
    cB
    inss1
    eqsstr3i
    sseli
    ofval.6
    sylan2
    @0
    wph
    cX
    cB
    wcel
    @11
    cD
    wceq
    cS
    cB
    cX
    cS
    @13
    cB
    offval.5
    cA
    cB
    inss2
    eqsstr3i
    sseli
    ofval.7
    sylan2
    oveq12d
    3eqtrd
end

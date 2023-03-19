include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "c1.mm"
include "wi.mm"
include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wrex.mm"
include "recex.mm"
include "syl2anc.mm"
include "wa.mm"
include "oveq2.mm"
include "simprl.mm"
include "adantr.mm"
include "mulcomd.mm"
include "simprr.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "mulassd.mm"
include "mulid2d.mm"
include "3eqtr3d.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "rexlimddv.mm"
include "impbid1.mm"

theorem mulcand
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  assume mulcand.1: |- ( ph -> A e. CC )
  assume mulcand.2: |- ( ph -> B e. CC )
  assume mulcand.3: |- ( ph -> C e. CC )
  assume mulcand.4: |- ( ph -> C =/= 0 )


  assert |- ( ph -> ( ( C x. A ) = ( C x. B ) <-> A = B ) )

  proof
    wph
    cC
    cA
    cmul
    co
    #
    cC
    cB
    cmul
    co
    #
    wceq
    #
    cA
    cB
    wceq
    #
    wph
    cC
    vx
    cv
    #
    cmul
    co
    #
    c1
    wceq
    #
    @2
    @3
    wi
    vx
    cc
    wph
    cC
    cc
    wcel
    #
    cC
    cc0
    wne
    @6
    vx
    cc
    wrex
    mulcand.3
    mulcand.4
    vx
    cC
    recex
    syl2anc
    @2
    @4
    @0
    cmul
    co
    #
    @4
    @1
    cmul
    co
    #
    wceq
    wph
    @4
    cc
    wcel
    #
    @6
    wa
    #
    wa
    #
    @3
    @0
    @1
    @4
    cmul
    oveq2
    @12
    @8
    cA
    @9
    cB
    @12
    @4
    cC
    cmul
    co
    #
    cA
    cmul
    co
    c1
    cA
    cmul
    co
    @8
    cA
    @12
    @13
    c1
    cA
    cmul
    @12
    @13
    @5
    c1
    @12
    @4
    cC
    wph
    @10
    @6
    simprl
    #
    wph
    @7
    @11
    mulcand.3
    adantr
    #
    mulcomd
    wph
    @10
    @6
    simprr
    eqtrd
    #
    oveq1d
    @12
    @4
    cC
    cA
    @14
    @15
    wph
    cA
    cc
    wcel
    @11
    mulcand.1
    adantr
    #
    mulassd
    @12
    cA
    @17
    mulid2d
    3eqtr3d
    @12
    @13
    cB
    cmul
    co
    c1
    cB
    cmul
    co
    @9
    cB
    @12
    @13
    c1
    cB
    cmul
    @16
    oveq1d
    @12
    @4
    cC
    cB
    @14
    @15
    wph
    cB
    cc
    wcel
    @11
    mulcand.2
    adantr
    #
    mulassd
    @12
    cB
    @18
    mulid2d
    3eqtr3d
    eqeq12d
    syl5ib
    rexlimddv
    cA
    cB
    cC
    cmul
    oveq2
    impbid1
end

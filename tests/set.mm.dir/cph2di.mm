include "co.mm"
include "csca.mm"
include "cfv.mm"
include "cplusg.mm"
include "caddc.mm"
include "eqid.mm"
include "ccph.mm"
include "wcel.mm"
include "cphl.mm"
include "cphphl.mm"
include "syl.mm"
include "ip2di.mm"
include "cclm.mm"
include "wceq.mm"
include "cphclm.mm"
include "clmadd.mm"
include "3syl.mm"
include "oveqd.mm"
include "oveq123d.mm"
include "eqtr4d.mm"

theorem cph2di
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.xi: class .,
  let cV: class V
  let cW: class W
  assume cphipcj.h: |- ., = ( .i ` W )
  assume cphipcj.v: |- V = ( Base ` W )
  assume cphdir.P: |- .+ = ( +g ` W )
  assume cph2di.1: |- ( ph -> W e. CPreHil )
  assume cph2di.2: |- ( ph -> A e. V )
  assume cph2di.3: |- ( ph -> B e. V )
  assume cph2di.4: |- ( ph -> C e. V )
  assume cph2di.5: |- ( ph -> D e. V )


  assert |- ( ph -> ( ( A .+ B ) ., ( C .+ D ) ) = ( ( ( A ., C ) + ( B ., D ) ) + ( ( A ., D ) + ( B ., C ) ) ) )

  proof
    wph
    cA
    cB
    c.pl
    co
    cC
    cD
    c.pl
    co
    c.xi
    co
    cA
    cC
    c.xi
    co
    #
    cB
    cD
    c.xi
    co
    #
    cW
    csca
    cfv
    #
    cplusg
    cfv
    #
    co
    #
    cA
    cD
    c.xi
    co
    #
    cB
    cC
    c.xi
    co
    #
    @3
    co
    #
    @3
    co
    @0
    @1
    caddc
    co
    #
    @5
    @6
    caddc
    co
    #
    caddc
    co
    wph
    cA
    cB
    cC
    cD
    c.pl
    @3
    @2
    c.xi
    cV
    cW
    @2
    eqid
    #
    cphipcj.h
    cphipcj.v
    cphdir.P
    @3
    eqid
    wph
    cW
    ccph
    wcel
    #
    cW
    cphl
    wcel
    cph2di.1
    cW
    cphphl
    syl
    cph2di.2
    cph2di.3
    cph2di.4
    cph2di.5
    ip2di
    wph
    @8
    @4
    @9
    @7
    caddc
    @3
    wph
    @11
    cW
    cclm
    wcel
    caddc
    @3
    wceq
    cph2di.1
    cW
    cphclm
    @2
    cW
    @10
    clmadd
    3syl
    #
    wph
    caddc
    @3
    @0
    @1
    @12
    oveqd
    wph
    caddc
    @3
    @5
    @6
    @12
    oveqd
    oveq123d
    eqtr4d
end

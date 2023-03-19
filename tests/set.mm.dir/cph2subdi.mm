include "co.mm"
include "caddc.mm"
include "csca.mm"
include "cfv.mm"
include "csg.mm"
include "cplusg.mm"
include "cmin.mm"
include "cclm.mm"
include "wcel.mm"
include "wceq.mm"
include "ccph.mm"
include "cphclm.mm"
include "syl.mm"
include "eqid.mm"
include "clmadd.mm"
include "oveqd.mm"
include "oveq12d.mm"
include "cbs.mm"
include "cphl.mm"
include "cphphl.mm"
include "ipcl.mm"
include "syl3anc.mm"
include "clmacl.mm"
include "clmsub.mm"
include "ip2subdi.mm"
include "3eqtr4rd.mm"

theorem cph2subdi
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.xi: class .,
  let c.mi: class .-
  let cV: class V
  let cW: class W
  assume cphipcj.h: |- ., = ( .i ` W )
  assume cphipcj.v: |- V = ( Base ` W )
  assume cphsubdir.m: |- .- = ( -g ` W )
  assume cph2subdi.1: |- ( ph -> W e. CPreHil )
  assume cph2subdi.2: |- ( ph -> A e. V )
  assume cph2subdi.3: |- ( ph -> B e. V )
  assume cph2subdi.4: |- ( ph -> C e. V )
  assume cph2subdi.5: |- ( ph -> D e. V )


  assert |- ( ph -> ( ( A .- B ) ., ( C .- D ) ) = ( ( ( A ., C ) + ( B ., D ) ) - ( ( A ., D ) + ( B ., C ) ) ) )

  proof
    wph
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
    caddc
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
    caddc
    co
    #
    cW
    csca
    cfv
    #
    csg
    cfv
    #
    co
    #
    @0
    @1
    @6
    cplusg
    cfv
    #
    co
    #
    @3
    @4
    @9
    co
    #
    @7
    co
    @2
    @5
    cmin
    co
    #
    cA
    cB
    c.mi
    co
    cC
    cD
    c.mi
    co
    c.xi
    co
    wph
    @2
    @10
    @5
    @11
    @7
    wph
    caddc
    @9
    @0
    @1
    wph
    cW
    cclm
    wcel
    #
    caddc
    @9
    wceq
    wph
    cW
    ccph
    wcel
    #
    @13
    cph2subdi.1
    cW
    cphclm
    syl
    #
    @6
    cW
    @6
    eqid
    #
    clmadd
    syl
    #
    oveqd
    wph
    caddc
    @9
    @3
    @4
    @17
    oveqd
    oveq12d
    wph
    @13
    @2
    @6
    cbs
    cfv
    #
    wcel
    #
    @5
    @18
    wcel
    #
    @12
    @8
    wceq
    @15
    wph
    @13
    @0
    @18
    wcel
    #
    @1
    @18
    wcel
    #
    @19
    @15
    wph
    cW
    cphl
    wcel
    #
    cA
    cV
    wcel
    #
    cC
    cV
    wcel
    #
    @21
    wph
    @14
    @23
    cph2subdi.1
    cW
    cphphl
    syl
    #
    cph2subdi.2
    cph2subdi.4
    cA
    cC
    @6
    c.xi
    @18
    cV
    cW
    @16
    cphipcj.h
    cphipcj.v
    @18
    eqid
    #
    ipcl
    syl3anc
    wph
    @23
    cB
    cV
    wcel
    #
    cD
    cV
    wcel
    #
    @22
    @26
    cph2subdi.3
    cph2subdi.5
    cB
    cD
    @6
    c.xi
    @18
    cV
    cW
    @16
    cphipcj.h
    cphipcj.v
    @27
    ipcl
    syl3anc
    @6
    @18
    cW
    @0
    @1
    @16
    @27
    clmacl
    syl3anc
    wph
    @13
    @3
    @18
    wcel
    #
    @4
    @18
    wcel
    #
    @20
    @15
    wph
    @23
    @24
    @29
    @30
    @26
    cph2subdi.2
    cph2subdi.5
    cA
    cD
    @6
    c.xi
    @18
    cV
    cW
    @16
    cphipcj.h
    cphipcj.v
    @27
    ipcl
    syl3anc
    wph
    @23
    @28
    @25
    @31
    @26
    cph2subdi.3
    cph2subdi.4
    cB
    cC
    @6
    c.xi
    @18
    cV
    cW
    @16
    cphipcj.h
    cphipcj.v
    @27
    ipcl
    syl3anc
    @6
    @18
    cW
    @3
    @4
    @16
    @27
    clmacl
    syl3anc
    @2
    @5
    @6
    @18
    cW
    @16
    @27
    clmsub
    syl3anc
    wph
    cA
    cB
    cC
    cD
    @9
    @7
    @6
    c.xi
    c.mi
    cV
    cW
    @16
    cphipcj.h
    cphipcj.v
    cphsubdir.m
    @7
    eqid
    @9
    eqid
    @26
    cph2subdi.2
    cph2subdi.3
    cph2subdi.4
    cph2subdi.5
    ip2subdi
    3eqtr4rd
end

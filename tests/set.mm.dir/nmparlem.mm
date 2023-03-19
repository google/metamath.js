include "co.mm"
include "caddc.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "cmul.mm"
include "cmin.mm"
include "cph2di.mm"
include "cph2subdi.mm"
include "oveq12d.mm"
include "cc.mm"
include "cclm.mm"
include "wcel.mm"
include "wss.mm"
include "ccph.mm"
include "cphclm.mm"
include "syl.mm"
include "clmsscn.mm"
include "cphl.mm"
include "cphphl.mm"
include "ipcl.mm"
include "syl3anc.mm"
include "clmacl.mm"
include "sseldd.mm"
include "ppncand.mm"
include "eqtrd.mm"
include "wceq.mm"
include "clmod.mm"
include "cphlmod.mm"
include "lmodvacl.mm"
include "nmsq.mm"
include "syl2anc.mm"
include "lmodvsubcl.mm"
include "oveq2d.mm"
include "2timesd.mm"
include "3eqtr4d.mm"

theorem nmparlem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cF: class F
  let c.xi: class .,
  let cK: class K
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  assume nmpar.v: |- V = ( Base ` W )
  assume nmpar.p: |- .+ = ( +g ` W )
  assume nmpar.m: |- .- = ( -g ` W )
  assume nmpar.n: |- N = ( norm ` W )
  assume nmpar.h: |- ., = ( .i ` W )
  assume nmpar.f: |- F = ( Scalar ` W )
  assume nmpar.k: |- K = ( Base ` F )
  assume nmpar.1: |- ( ph -> W e. CPreHil )
  assume nmpar.2: |- ( ph -> A e. V )
  assume nmpar.3: |- ( ph -> B e. V )


  assert |- ( ph -> ( ( ( N ` ( A .+ B ) ) ^ 2 ) + ( ( N ` ( A .- B ) ) ^ 2 ) ) = ( 2 x. ( ( ( N ` A ) ^ 2 ) + ( ( N ` B ) ^ 2 ) ) ) )

  proof
    wph
    cA
    cB
    c.pl
    co
    #
    @0
    c.xi
    co
    #
    cA
    cB
    c.mi
    co
    #
    @2
    c.xi
    co
    #
    caddc
    co
    #
    cA
    cA
    c.xi
    co
    #
    cB
    cB
    c.xi
    co
    #
    caddc
    co
    #
    @7
    caddc
    co
    #
    @0
    cN
    cfv
    c2
    cexp
    co
    #
    @2
    cN
    cfv
    c2
    cexp
    co
    #
    caddc
    co
    c2
    cA
    cN
    cfv
    c2
    cexp
    co
    #
    cB
    cN
    cfv
    c2
    cexp
    co
    #
    caddc
    co
    #
    cmul
    co
    #
    wph
    @4
    @7
    cA
    cB
    c.xi
    co
    #
    cB
    cA
    c.xi
    co
    #
    caddc
    co
    #
    caddc
    co
    #
    @7
    @17
    cmin
    co
    #
    caddc
    co
    @8
    wph
    @1
    @18
    @3
    @19
    caddc
    wph
    cA
    cB
    cA
    cB
    c.pl
    c.xi
    cV
    cW
    nmpar.h
    nmpar.v
    nmpar.p
    nmpar.1
    nmpar.2
    nmpar.3
    nmpar.2
    nmpar.3
    cph2di
    wph
    cA
    cB
    cA
    cB
    c.xi
    c.mi
    cV
    cW
    nmpar.h
    nmpar.v
    nmpar.m
    nmpar.1
    nmpar.2
    nmpar.3
    nmpar.2
    nmpar.3
    cph2subdi
    oveq12d
    wph
    @7
    @17
    @7
    wph
    cK
    cc
    @7
    wph
    cW
    cclm
    wcel
    #
    cK
    cc
    wss
    wph
    cW
    ccph
    wcel
    #
    @20
    nmpar.1
    cW
    cphclm
    syl
    #
    cF
    cK
    cW
    nmpar.f
    nmpar.k
    clmsscn
    syl
    #
    wph
    @20
    @5
    cK
    wcel
    #
    @6
    cK
    wcel
    #
    @7
    cK
    wcel
    @22
    wph
    cW
    cphl
    wcel
    #
    cA
    cV
    wcel
    #
    @27
    @24
    wph
    @21
    @26
    nmpar.1
    cW
    cphphl
    syl
    #
    nmpar.2
    nmpar.2
    cA
    cA
    cF
    c.xi
    cK
    cV
    cW
    nmpar.f
    nmpar.h
    nmpar.v
    nmpar.k
    ipcl
    syl3anc
    wph
    @26
    cB
    cV
    wcel
    #
    @29
    @25
    @28
    nmpar.3
    nmpar.3
    cB
    cB
    cF
    c.xi
    cK
    cV
    cW
    nmpar.f
    nmpar.h
    nmpar.v
    nmpar.k
    ipcl
    syl3anc
    cF
    cK
    cW
    @5
    @6
    nmpar.f
    nmpar.k
    clmacl
    syl3anc
    sseldd
    #
    wph
    cK
    cc
    @17
    @23
    wph
    @20
    @15
    cK
    wcel
    #
    @16
    cK
    wcel
    #
    @17
    cK
    wcel
    @22
    wph
    @26
    @27
    @29
    @31
    @28
    nmpar.2
    nmpar.3
    cA
    cB
    cF
    c.xi
    cK
    cV
    cW
    nmpar.f
    nmpar.h
    nmpar.v
    nmpar.k
    ipcl
    syl3anc
    wph
    @26
    @29
    @27
    @32
    @28
    nmpar.3
    nmpar.2
    cB
    cA
    cF
    c.xi
    cK
    cV
    cW
    nmpar.f
    nmpar.h
    nmpar.v
    nmpar.k
    ipcl
    syl3anc
    cF
    cK
    cW
    @15
    @16
    nmpar.f
    nmpar.k
    clmacl
    syl3anc
    sseldd
    @30
    ppncand
    eqtrd
    wph
    @9
    @1
    @10
    @3
    caddc
    wph
    @21
    @0
    cV
    wcel
    #
    @9
    @1
    wceq
    nmpar.1
    wph
    cW
    clmod
    wcel
    #
    @27
    @29
    @33
    wph
    @21
    @34
    nmpar.1
    cW
    cphlmod
    syl
    #
    nmpar.2
    nmpar.3
    c.pl
    cV
    cW
    cA
    cB
    nmpar.v
    nmpar.p
    lmodvacl
    syl3anc
    @0
    c.xi
    cN
    cV
    cW
    nmpar.v
    nmpar.h
    nmpar.n
    nmsq
    syl2anc
    wph
    @21
    @2
    cV
    wcel
    #
    @10
    @3
    wceq
    nmpar.1
    wph
    @34
    @27
    @29
    @36
    @35
    nmpar.2
    nmpar.3
    c.mi
    cV
    cW
    cA
    cB
    nmpar.v
    nmpar.m
    lmodvsubcl
    syl3anc
    @2
    c.xi
    cN
    cV
    cW
    nmpar.v
    nmpar.h
    nmpar.n
    nmsq
    syl2anc
    oveq12d
    wph
    @14
    c2
    @7
    cmul
    co
    @8
    wph
    @13
    @7
    c2
    cmul
    wph
    @11
    @5
    @12
    @6
    caddc
    wph
    @21
    @27
    @11
    @5
    wceq
    nmpar.1
    nmpar.2
    cA
    c.xi
    cN
    cV
    cW
    nmpar.v
    nmpar.h
    nmpar.n
    nmsq
    syl2anc
    wph
    @21
    @29
    @12
    @6
    wceq
    nmpar.1
    nmpar.3
    cB
    c.xi
    cN
    cV
    cW
    nmpar.v
    nmpar.h
    nmpar.n
    nmsq
    syl2anc
    oveq12d
    oveq2d
    wph
    @7
    @30
    2timesd
    eqtrd
    3eqtr4d
end

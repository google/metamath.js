include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "c1.mm"
include "cneg.mm"
include "cns.mm"
include "cfv.mm"
include "co.mm"
include "cpv.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "cc.mm"
include "neg1cn.mm"
include "eqid.mm"
include "nvscl.mm"
include "mp3an2.mm"
include "3adant2.mm"
include "nvtri.mm"
include "syld3an3.mm"
include "nvmval.mm"
include "fveq2d.mm"
include "wceq.mm"
include "wa.mm"
include "cabs.mm"
include "cmul.mm"
include "nvs.mm"
include "ax-1cn.mm"
include "absnegi.mm"
include "abs1.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "nvcl.mm"
include "recnd.mm"
include "mulid2d.mm"
include "syl5eq.mm"
include "eqtr2d.mm"
include "oveq2d.mm"
include "3brtr4d.mm"

theorem nvmtri
  let cA: class A
  let cB: class B
  let cU: class U
  let cM: class M
  let cN: class N
  let cX: class X
  assume nvmtri.1: |- X = ( BaseSet ` U )
  assume nvmtri.3: |- M = ( -v ` U )
  assume nvmtri.6: |- N = ( normCV ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( N ` ( A M B ) ) <_ ( ( N ` A ) + ( N ` B ) ) )

  proof
    cU
    cnv
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cA
    c1
    cneg
    #
    cB
    cU
    cns
    cfv
    #
    co
    #
    cU
    cpv
    cfv
    #
    co
    #
    cN
    cfv
    #
    cA
    cN
    cfv
    #
    @6
    cN
    cfv
    #
    caddc
    co
    #
    cA
    cB
    cM
    co
    #
    cN
    cfv
    @10
    cB
    cN
    cfv
    #
    caddc
    co
    cle
    @0
    @1
    @2
    @6
    cX
    wcel
    #
    @9
    @12
    cle
    wbr
    @0
    @2
    @15
    @1
    @0
    @4
    cc
    wcel
    #
    @2
    @15
    neg1cn
    @4
    cB
    @5
    cU
    cX
    nvmtri.1
    @5
    eqid
    #
    nvscl
    mp3an2
    3adant2
    cA
    @6
    cU
    @7
    cN
    cX
    nvmtri.1
    @7
    eqid
    #
    nvmtri.6
    nvtri
    syld3an3
    @3
    @13
    @8
    cN
    cA
    cB
    @5
    cU
    @7
    cM
    cX
    nvmtri.1
    @18
    @17
    nvmtri.3
    nvmval
    fveq2d
    @3
    @14
    @11
    @10
    caddc
    @0
    @2
    @14
    @11
    wceq
    @1
    @0
    @2
    wa
    #
    @11
    @4
    cabs
    cfv
    #
    @14
    cmul
    co
    #
    @14
    @0
    @16
    @2
    @11
    @21
    wceq
    neg1cn
    @4
    cB
    @5
    cU
    cN
    cX
    nvmtri.1
    @17
    nvmtri.6
    nvs
    mp3an2
    @19
    @21
    c1
    @14
    cmul
    co
    @14
    @20
    c1
    @14
    cmul
    @20
    c1
    cabs
    cfv
    c1
    c1
    ax-1cn
    absnegi
    abs1
    eqtri
    oveq1i
    @19
    @14
    @19
    @14
    cB
    cU
    cN
    cX
    nvmtri.1
    nvmtri.6
    nvcl
    recnd
    mulid2d
    syl5eq
    eqtr2d
    3adant2
    oveq2d
    3brtr4d
end

include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "c1.mm"
include "cneg.mm"
include "csn.mm"
include "cxp.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "caddc.mm"
include "cdgr.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cmin.mm"
include "plyssc.mm"
include "sseli.mm"
include "wss.mm"
include "ssid.mm"
include "neg1cn.mm"
include "plyconst.mm"
include "mp2an.mm"
include "plymulcl.mm"
include "sylancr.mm"
include "eqid.mm"
include "dgradd.mm"
include "syl2an.mm"
include "wf.mm"
include "wceq.mm"
include "plyf.mm"
include "cvv.mm"
include "cnex.mm"
include "ofnegsub.mm"
include "mp3an1.mm"
include "fveq2d.mm"
include "cc0.mm"
include "wne.mm"
include "neg1ne0.mm"
include "dgrmulc.mm"
include "mp3an12.mm"
include "syl6eqr.mm"
include "adantl.mm"
include "breq2d.mm"
include "ifbieq1d.mm"
include "3brtr3d.mm"

theorem dgrsub
  let cS: class S
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  assume dgrsub.1: |- M = ( deg ` F )
  assume dgrsub.2: |- N = ( deg ` G )


  assert |- ( ( F e. ( Poly ` S ) /\ G e. ( Poly ` S ) ) -> ( deg ` ( F oF - G ) ) <_ if ( M <_ N , N , M ) )

  proof
    cF
    cS
    cply
    cfv
    #
    wcel
    #
    cG
    @0
    wcel
    #
    wa
    #
    cF
    cc
    c1
    cneg
    #
    csn
    cxp
    #
    cG
    cmul
    cof
    co
    #
    caddc
    cof
    co
    #
    cdgr
    cfv
    #
    cM
    @6
    cdgr
    cfv
    #
    cle
    wbr
    #
    @9
    cM
    cif
    #
    cF
    cG
    cmin
    cof
    co
    #
    cdgr
    cfv
    cM
    cN
    cle
    wbr
    #
    cN
    cM
    cif
    cle
    @1
    cF
    cc
    cply
    cfv
    #
    wcel
    @6
    @14
    wcel
    #
    @8
    @11
    cle
    wbr
    @2
    @0
    @14
    cF
    cS
    plyssc
    #
    sseli
    @2
    @5
    @14
    wcel
    #
    cG
    @14
    wcel
    @15
    cc
    cc
    wss
    @4
    cc
    wcel
    #
    @17
    cc
    ssid
    neg1cn
    @4
    cc
    plyconst
    mp2an
    @0
    @14
    cG
    @16
    sseli
    cc
    @5
    cG
    plymulcl
    sylancr
    cc
    cF
    @6
    cM
    @9
    dgrsub.1
    @9
    eqid
    dgradd
    syl2an
    @3
    @7
    @12
    cdgr
    @1
    cc
    cc
    cF
    wf
    #
    cc
    cc
    cG
    wf
    #
    @7
    @12
    wceq
    #
    @2
    cS
    cF
    plyf
    cS
    cG
    plyf
    cc
    cvv
    wcel
    @19
    @20
    @21
    cnex
    cc
    cF
    cG
    cvv
    ofnegsub
    mp3an1
    syl2an
    fveq2d
    @3
    @10
    @13
    @9
    cN
    cM
    @3
    @9
    cN
    cM
    cle
    @2
    @9
    cN
    wceq
    @1
    @2
    @9
    cG
    cdgr
    cfv
    #
    cN
    @18
    @4
    cc0
    wne
    @2
    @9
    @22
    wceq
    neg1cn
    neg1ne0
    @4
    cS
    cG
    dgrmulc
    mp3an12
    dgrsub.2
    syl6eqr
    adantl
    #
    breq2d
    @23
    ifbieq1d
    3brtr3d
end

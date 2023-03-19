include "wcel.mm"
include "w3a.mm"
include "cnsb.mm"
include "cfv.mm"
include "co.mm"
include "cnmcv.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cnv.mm"
include "eqid.mm"
include "nvmcl.mm"
include "mp3an1.mm"
include "nmblolbi.mm"
include "sylan2.mm"
include "3impb.mm"
include "wceq.mm"
include "wf.mm"
include "blof.mm"
include "mp3an12.mm"
include "ffvelrnda.mm"
include "3adant3.mm"
include "3adant2.mm"
include "imsdval.mm"
include "syl2anc.mm"
include "clno.mm"
include "bloln.mm"
include "lnosub.mm"
include "mp3anl1.mm"
include "mpanl1.mm"
include "syl3an1.mm"
include "fveq2d.mm"
include "eqtr4d.mm"
include "3adant1.mm"
include "oveq2d.mm"
include "3brtr4d.mm"

theorem blometi
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cU: class U
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  assume blometi.1: |- X = ( BaseSet ` U )
  assume blometi.2: |- Y = ( BaseSet ` W )
  assume blometi.8: |- C = ( IndMet ` U )
  assume blometi.d: |- D = ( IndMet ` W )
  assume blometi.6: |- N = ( U normOpOLD W )
  assume blometi.7: |- B = ( U BLnOp W )
  assume blometi.u: |- U e. NrmCVec
  assume blometi.w: |- W e. NrmCVec


  assert |- ( ( T e. B /\ P e. X /\ Q e. X ) -> ( ( T ` P ) D ( T ` Q ) ) <_ ( ( N ` T ) x. ( P C Q ) ) )

  proof
    cT
    cB
    wcel
    #
    cP
    cX
    wcel
    #
    cQ
    cX
    wcel
    #
    w3a
    #
    cP
    cQ
    cU
    cnsb
    cfv
    #
    co
    #
    cT
    cfv
    #
    cW
    cnmcv
    cfv
    #
    cfv
    #
    cT
    cN
    cfv
    #
    @5
    cU
    cnmcv
    cfv
    #
    cfv
    #
    cmul
    co
    #
    cP
    cT
    cfv
    #
    cQ
    cT
    cfv
    #
    cD
    co
    #
    @9
    cP
    cQ
    cC
    co
    #
    cmul
    co
    cle
    @0
    @1
    @2
    @8
    @12
    cle
    wbr
    #
    @1
    @2
    wa
    #
    @0
    @5
    cX
    wcel
    #
    @17
    cU
    cnv
    wcel
    #
    @1
    @2
    @19
    blometi.u
    cP
    cQ
    cU
    @4
    cX
    blometi.1
    @4
    eqid
    #
    nvmcl
    mp3an1
    @5
    cB
    cT
    cU
    @10
    @7
    cN
    cW
    cX
    blometi.1
    @10
    eqid
    #
    @7
    eqid
    #
    blometi.6
    blometi.7
    blometi.u
    blometi.w
    nmblolbi
    sylan2
    3impb
    @3
    @15
    @13
    @14
    cW
    cnsb
    cfv
    #
    co
    #
    @7
    cfv
    #
    @8
    @3
    @13
    cY
    wcel
    #
    @14
    cY
    wcel
    #
    @15
    @26
    wceq
    #
    @0
    @1
    @27
    @2
    @0
    cX
    cY
    cP
    cT
    @20
    cW
    cnv
    wcel
    #
    @0
    cX
    cY
    cT
    wf
    blometi.u
    blometi.w
    cB
    cT
    cU
    cW
    cX
    cY
    blometi.1
    blometi.2
    blometi.7
    blof
    mp3an12
    #
    ffvelrnda
    3adant3
    @0
    @2
    @28
    @1
    @0
    cX
    cY
    cQ
    cT
    @31
    ffvelrnda
    3adant2
    @30
    @27
    @28
    @29
    blometi.w
    @13
    @14
    cD
    cW
    @24
    @7
    cY
    blometi.2
    @24
    eqid
    #
    @23
    blometi.d
    imsdval
    mp3an1
    syl2anc
    @3
    @6
    @25
    @7
    @0
    cT
    cU
    cW
    clno
    co
    #
    wcel
    #
    @1
    @2
    @6
    @25
    wceq
    #
    @20
    @30
    @0
    @34
    blometi.u
    blometi.w
    cB
    cT
    cU
    @33
    cW
    @33
    eqid
    #
    blometi.7
    bloln
    mp3an12
    @34
    @1
    @2
    @35
    @30
    @34
    @18
    @35
    blometi.w
    @20
    @30
    @34
    @18
    @35
    blometi.u
    cP
    cQ
    cT
    cU
    @33
    @4
    @24
    cW
    cX
    blometi.1
    @21
    @32
    @36
    lnosub
    mp3anl1
    mpanl1
    3impb
    syl3an1
    fveq2d
    eqtr4d
    @3
    @16
    @11
    @9
    cmul
    @1
    @2
    @16
    @11
    wceq
    #
    @0
    @20
    @1
    @2
    @37
    blometi.u
    cP
    cQ
    cC
    cU
    @4
    @10
    cX
    blometi.1
    @21
    @22
    blometi.8
    imsdval
    mp3an1
    3adant1
    oveq2d
    3brtr4d
end

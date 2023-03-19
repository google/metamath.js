include "cnv.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "c1.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "simp1.mm"
include "nvcl.mm"
include "3adant3.mm"
include "wa.mm"
include "nvz.mm"
include "necon3bid.mm"
include "biimp3ar.mm"
include "rereccld.mm"
include "clt.mm"
include "nvgt0.mm"
include "biimp3a.mm"
include "1re.mm"
include "0le1.mm"
include "divge0.mm"
include "mpanl12.mm"
include "syl2anc.mm"
include "simp2.mm"
include "nvsge0.mm"
include "syl121anc.mm"
include "cc.mm"
include "recnd.mm"
include "recid2d.mm"
include "eqtrd.mm"

theorem nv1
  let cA: class A
  let cS: class S
  let cU: class U
  let cN: class N
  let cX: class X
  let cZ: class Z
  assume nv1.1: |- X = ( BaseSet ` U )
  assume nv1.4: |- S = ( .sOLD ` U )
  assume nv1.5: |- Z = ( 0vec ` U )
  assume nv1.6: |- N = ( normCV ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X /\ A =/= Z ) -> ( N ` ( ( 1 / ( N ` A ) ) S A ) ) = 1 )

  proof
    cU
    cnv
    wcel
    #
    cA
    cX
    wcel
    #
    cA
    cZ
    wne
    #
    w3a
    #
    c1
    cA
    cN
    cfv
    #
    cdiv
    co
    #
    cA
    cS
    co
    cN
    cfv
    #
    @5
    @4
    cmul
    co
    #
    c1
    @3
    @0
    @5
    cr
    wcel
    cc0
    @5
    cle
    wbr
    #
    @1
    @6
    @7
    wceq
    @0
    @1
    @2
    simp1
    @3
    @4
    @0
    @1
    @4
    cr
    wcel
    #
    @2
    cA
    cU
    cN
    cX
    nv1.1
    nv1.6
    nvcl
    #
    3adant3
    #
    @0
    @1
    @4
    cc0
    wne
    @2
    @0
    @1
    wa
    #
    @4
    cc0
    cA
    cZ
    cA
    cU
    cN
    cX
    cZ
    nv1.1
    nv1.5
    nv1.6
    nvz
    necon3bid
    biimp3ar
    #
    rereccld
    @3
    @9
    cc0
    @4
    clt
    wbr
    #
    @8
    @11
    @0
    @1
    @2
    @14
    cA
    cU
    cN
    cX
    cZ
    nv1.1
    nv1.5
    nv1.6
    nvgt0
    biimp3a
    c1
    cr
    wcel
    cc0
    c1
    cle
    wbr
    @9
    @14
    wa
    @8
    1re
    0le1
    c1
    @4
    divge0
    mpanl12
    syl2anc
    @0
    @1
    @2
    simp2
    @5
    cA
    cS
    cU
    cN
    cX
    nv1.1
    nv1.4
    nv1.6
    nvsge0
    syl121anc
    @3
    @4
    @0
    @1
    @4
    cc
    wcel
    @2
    @12
    @4
    @10
    recnd
    3adant3
    @13
    recid2d
    eqtrd
end

include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "cn.mm"
include "wral.mm"
include "wa.mm"
include "ciun.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "dfiun2g.mm"
include "adantl.mm"
include "cpw.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "simpl.mm"
include "wss.mm"
include "abid.mm"
include "wi.mm"
include "eleq1a.mm"
include "ralimi.mm"
include "r19.23v.mm"
include "sylib.mm"
include "imp.mm"
include "adantll.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "nfab1.mm"
include "nfcv.mm"
include "dfss3f.mm"
include "sylibr.mm"
include "wb.mm"
include "elpw2g.mm"
include "adantr.mm"
include "mpbird.mm"
include "nnct.mm"
include "abrexct.mm"
include "mp1i.mm"
include "sigaclcu.mm"
include "syl3anc.mm"
include "eqeltrd.mm"

theorem sigaclcu2
  let cA: class A
  let cS: class S
  let vk: setvar k
  let vo: setvar o
  let vs: setvar s
  let vx: setvar x

  disjoint S k
  disjoint o s
  disjoint o x
  disjoint S o
  disjoint s x
  disjoint S s
  disjoint S x
  disjoint A x
  disjoint k x
  assert |- ( ( S e. U. ran sigAlgebra /\ A. k e. NN A e. S ) -> U_ k e. NN A e. S )

  proof
    cS
    csiga
    crn
    cuni
    #
    wcel
    #
    cA
    cS
    wcel
    #
    vk
    cn
    wral
    #
    wa
    #
    vk
    cn
    cA
    ciun
    #
    vx
    cv
    #
    cA
    wceq
    #
    vk
    cn
    wrex
    #
    vx
    cab
    #
    cuni
    #
    cS
    @3
    @5
    @10
    wceq
    @1
    vk
    vx
    cn
    cA
    cS
    dfiun2g
    adantl
    @4
    @1
    @9
    cS
    cpw
    wcel
    #
    @9
    com
    cdom
    wbr
    #
    @10
    cS
    wcel
    @1
    @3
    simpl
    @4
    @11
    @9
    cS
    wss
    #
    @4
    @6
    cS
    wcel
    #
    vx
    @9
    wral
    @13
    @4
    @14
    vx
    @9
    @6
    @9
    wcel
    @4
    @8
    @14
    @8
    vx
    abid
    @3
    @8
    @14
    @1
    @3
    @8
    @14
    @3
    @7
    @14
    wi
    #
    vk
    cn
    wral
    @8
    @14
    wi
    @2
    @15
    vk
    cn
    cA
    cS
    @6
    eleq1a
    ralimi
    @7
    @14
    vk
    cn
    r19.23v
    sylib
    imp
    adantll
    sylan2b
    ralrimiva
    vx
    @9
    cS
    @8
    vx
    nfab1
    vx
    cS
    nfcv
    dfss3f
    sylibr
    @1
    @11
    @13
    wb
    @3
    @9
    cS
    @0
    elpw2g
    adantr
    mpbird
    cn
    com
    cdom
    wbr
    @12
    @4
    nnct
    vk
    vx
    cn
    cA
    abrexct
    mp1i
    @9
    cS
    sigaclcu
    syl3anc
    eqeltrd
end

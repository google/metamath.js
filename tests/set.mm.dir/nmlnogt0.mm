include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "nmlno0.mm"
include "necon3bid.mm"
include "cba.mm"
include "wf.mm"
include "wb.mm"
include "eqid.mm"
include "lnof.mm"
include "cxr.mm"
include "cle.mm"
include "nmoxr.mm"
include "nmooge0.mm"
include "wa.mm"
include "wo.mm"
include "0xr.mm"
include "xrlttri2.mm"
include "mpan2.mm"
include "adantr.mm"
include "wn.mm"
include "xrlenlt.mm"
include "mpan.mm"
include "biimpa.mm"
include "biorf.mm"
include "syl.mm"
include "bitr4d.mm"
include "syl2anc.mm"
include "syld3an3.mm"
include "bitr3d.mm"

theorem nmlnogt0
  let cT: class T
  let cU: class U
  let cL: class L
  let cN: class N
  let cW: class W
  let cZ: class Z
  assume nmlnogt0.3: |- N = ( U normOpOLD W )
  assume nmlnogt0.0: |- Z = ( U 0op W )
  assume nmlnogt0.7: |- L = ( U LnOp W )


  assert |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L ) -> ( T =/= Z <-> 0 < ( N ` T ) ) )

  proof
    cU
    cnv
    wcel
    #
    cW
    cnv
    wcel
    #
    cT
    cL
    wcel
    #
    w3a
    #
    cT
    cN
    cfv
    #
    cc0
    wne
    #
    cT
    cZ
    wne
    cc0
    @4
    clt
    wbr
    #
    @3
    @4
    cc0
    cT
    cZ
    cT
    cU
    cL
    cN
    cW
    cZ
    nmlnogt0.3
    nmlnogt0.0
    nmlnogt0.7
    nmlno0
    necon3bid
    @0
    @1
    @2
    cU
    cba
    cfv
    #
    cW
    cba
    cfv
    #
    cT
    wf
    #
    @5
    @6
    wb
    #
    cT
    cU
    cL
    cW
    @7
    @8
    @7
    eqid
    #
    @8
    eqid
    #
    nmlnogt0.7
    lnof
    @0
    @1
    @9
    w3a
    @4
    cxr
    wcel
    #
    cc0
    @4
    cle
    wbr
    #
    @10
    cT
    cU
    cN
    cW
    @7
    @8
    @11
    @12
    nmlnogt0.3
    nmoxr
    cT
    cU
    cN
    cW
    @7
    @8
    @11
    @12
    nmlnogt0.3
    nmooge0
    @13
    @14
    wa
    #
    @5
    @4
    cc0
    clt
    wbr
    #
    @6
    wo
    #
    @6
    @13
    @5
    @17
    wb
    #
    @14
    @13
    cc0
    cxr
    wcel
    #
    @18
    0xr
    @4
    cc0
    xrlttri2
    mpan2
    adantr
    @15
    @16
    wn
    #
    @6
    @17
    wb
    @13
    @14
    @20
    @19
    @13
    @14
    @20
    wb
    0xr
    cc0
    @4
    xrlenlt
    mpan
    biimpa
    @16
    @6
    biorf
    syl
    bitr4d
    syl2anc
    syld3an3
    bitr3d
end

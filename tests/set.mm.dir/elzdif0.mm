include "cz.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "wceq.mm"
include "wn.mm"
include "cn.mm"
include "cneg.mm"
include "wo.mm"
include "eldifi.mm"
include "eldifn.mm"
include "elsng.mm"
include "notbid.mm"
include "biimpa.mm"
include "syl2anc.mm"
include "w3o.mm"
include "cr.mm"
include "wa.mm"
include "elz.mm"
include "sylib.mm"
include "simprd.mm"
include "3orass.mm"
include "orel1.mm"
include "sylc.mm"

theorem elzdif0
  let cM: class M


  assert |- ( M e. ( ZZ \ { 0 } ) -> ( M e. NN \/ -u M e. NN ) )

  proof
    cM
    cz
    cc0
    csn
    #
    cdif
    wcel
    #
    cM
    cc0
    wceq
    #
    wn
    #
    @2
    cM
    cn
    wcel
    #
    cM
    cneg
    cn
    wcel
    #
    wo
    #
    wo
    #
    @6
    @1
    cM
    cz
    wcel
    #
    cM
    @0
    wcel
    #
    wn
    #
    @3
    cM
    cz
    @0
    eldifi
    #
    cM
    cz
    @0
    eldifn
    @8
    @10
    @3
    @8
    @9
    @2
    cM
    cc0
    cz
    elsng
    notbid
    biimpa
    syl2anc
    @1
    @2
    @4
    @5
    w3o
    #
    @7
    @1
    cM
    cr
    wcel
    #
    @12
    @1
    @8
    @13
    @12
    wa
    @11
    cM
    elz
    sylib
    simprd
    @2
    @4
    @5
    3orass
    sylib
    @2
    @6
    orel1
    sylc
end

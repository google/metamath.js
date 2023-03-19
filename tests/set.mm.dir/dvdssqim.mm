include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "c2.mm"
include "cexp.mm"
include "divides.mm"
include "wi.mm"
include "zsqcl.mm"
include "dvdsmul2.mm"
include "syl2anr.mm"
include "cc.mm"
include "zcn.mm"
include "sqmul.mm"
include "breqtrrd.mm"
include "oveq1.mm"
include "breq2d.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "adantr.mm"
include "sylbid.mm"

theorem dvdssqim
  let cM: class M
  let cN: class N
  let vk: setvar k


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M || N -> ( M ^ 2 ) || ( N ^ 2 ) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    cM
    cN
    cdvds
    wbr
    vk
    cv
    #
    cM
    cmul
    co
    #
    cN
    wceq
    #
    vk
    cz
    wrex
    #
    cM
    c2
    cexp
    co
    #
    cN
    c2
    cexp
    co
    #
    cdvds
    wbr
    #
    vk
    cM
    cN
    divides
    @0
    @5
    @8
    wi
    @1
    @0
    @4
    @8
    vk
    cz
    @0
    @2
    cz
    wcel
    #
    wa
    #
    @6
    @3
    c2
    cexp
    co
    #
    cdvds
    wbr
    @4
    @8
    @10
    @6
    @2
    c2
    cexp
    co
    #
    @6
    cmul
    co
    #
    @11
    cdvds
    @9
    @12
    cz
    wcel
    @6
    cz
    wcel
    @6
    @13
    cdvds
    wbr
    @0
    @2
    zsqcl
    cM
    zsqcl
    @12
    @6
    dvdsmul2
    syl2anr
    @9
    @2
    cc
    wcel
    cM
    cc
    wcel
    @11
    @13
    wceq
    @0
    @2
    zcn
    cM
    zcn
    @2
    cM
    sqmul
    syl2anr
    breqtrrd
    @4
    @11
    @7
    @6
    cdvds
    @3
    cN
    c2
    cexp
    oveq1
    breq2d
    syl5ibcom
    rexlimdva
    adantr
    sylbid
end

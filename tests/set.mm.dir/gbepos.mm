include "cgbe.mm"
include "wcel.mm"
include "ceven.mm"
include "cv.mm"
include "codd.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cprime.mm"
include "wrex.mm"
include "wa.mm"
include "cn.mm"
include "isgbe.mm"
include "wi.mm"
include "prmnn.mm"
include "nnaddcl.mm"
include "syl2an.mm"
include "eleq1.mm"
include "syl5ibr.mm"
include "3ad2ant3.mm"
include "com12.mm"
include "a1i.mm"
include "rexlimdvv.mm"
include "imp.mm"
include "sylbi.mm"

theorem gbepos
  let cZ: class Z
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. GoldbachEven -> Z e. NN )

  proof
    cZ
    cgbe
    wcel
    cZ
    ceven
    wcel
    #
    vp
    cv
    #
    codd
    wcel
    #
    vq
    cv
    #
    codd
    wcel
    #
    cZ
    @1
    @3
    caddc
    co
    #
    wceq
    #
    w3a
    #
    vq
    cprime
    wrex
    vp
    cprime
    wrex
    #
    wa
    cZ
    cn
    wcel
    #
    cZ
    vq
    vp
    isgbe
    @0
    @8
    @9
    @0
    @7
    @9
    vp
    vq
    cprime
    cprime
    @1
    cprime
    wcel
    #
    @3
    cprime
    wcel
    #
    wa
    #
    @7
    @9
    wi
    wi
    @0
    @7
    @12
    @9
    @6
    @2
    @12
    @9
    wi
    @4
    @12
    @9
    @6
    @5
    cn
    wcel
    #
    @10
    @1
    cn
    wcel
    @3
    cn
    wcel
    @13
    @11
    @1
    prmnn
    @3
    prmnn
    @1
    @3
    nnaddcl
    syl2an
    cZ
    @5
    cn
    eleq1
    syl5ibr
    3ad2ant3
    com12
    a1i
    rexlimdvv
    imp
    sylbi
end

include "cgbow.mm"
include "wcel.mm"
include "codd.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cprime.mm"
include "wrex.mm"
include "wa.mm"
include "cn.mm"
include "isgbow.mm"
include "wi.mm"
include "prmnn.mm"
include "anim12i.mm"
include "adantr.mm"
include "nnaddcl.mm"
include "syl.mm"
include "adantl.mm"
include "nnaddcld.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "a1i.mm"
include "rexlimdvv.mm"
include "imp.mm"
include "sylbi.mm"

theorem gbowpos
  let cZ: class Z
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. GoldbachOddW -> Z e. NN )

  proof
    cZ
    cgbow
    wcel
    cZ
    codd
    wcel
    #
    cZ
    vp
    cv
    #
    vq
    cv
    #
    caddc
    co
    #
    vr
    cv
    #
    caddc
    co
    #
    wceq
    #
    vr
    cprime
    wrex
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
    vr
    vq
    vp
    isgbow
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
    @2
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
    @12
    @6
    @9
    vr
    cprime
    @12
    @4
    cprime
    wcel
    #
    wa
    #
    @9
    @6
    @5
    cn
    wcel
    @14
    @3
    @4
    @14
    @1
    cn
    wcel
    #
    @2
    cn
    wcel
    #
    wa
    #
    @3
    cn
    wcel
    @12
    @17
    @13
    @10
    @15
    @11
    @16
    @1
    prmnn
    @2
    prmnn
    anim12i
    adantr
    @1
    @2
    nnaddcl
    syl
    @13
    @4
    cn
    wcel
    @12
    @4
    prmnn
    adantl
    nnaddcld
    cZ
    @5
    cn
    eleq1
    syl5ibrcom
    rexlimdva
    a1i
    rexlimdvv
    imp
    sylbi
end

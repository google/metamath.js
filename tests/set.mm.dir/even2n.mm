include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "cz.mm"
include "wcel.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "evenelz.mm"
include "wa.mm"
include "2z.mm"
include "a1i.mm"
include "id.mm"
include "zmulcld.mm"
include "adantr.mm"
include "wb.mm"
include "eleq1.mm"
include "adantl.mm"
include "mpbid.mm"
include "rexlimiva.mm"
include "divides.mm"
include "zcn.mm"
include "2cnd.mm"
include "mulcomd.mm"
include "eqeq1d.mm"
include "rexbiia.mm"
include "syl6bb.mm"
include "mpan.mm"
include "pm5.21nii.mm"

theorem even2n
  let vn: setvar n
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y

  disjoint N n
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint N k
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint N x
  disjoint N y
  assert |- ( 2 || N <-> E. n e. ZZ ( 2 x. n ) = N )

  proof
    c2
    cN
    cdvds
    wbr
    #
    cN
    cz
    wcel
    #
    c2
    vn
    cv
    #
    cmul
    co
    #
    cN
    wceq
    #
    vn
    cz
    wrex
    #
    cN
    evenelz
    @4
    @1
    vn
    cz
    @2
    cz
    wcel
    #
    @4
    wa
    @3
    cz
    wcel
    #
    @1
    @6
    @7
    @4
    @6
    c2
    @2
    c2
    cz
    wcel
    #
    @6
    2z
    a1i
    @6
    id
    zmulcld
    adantr
    @4
    @7
    @1
    wb
    @6
    @3
    cN
    cz
    eleq1
    adantl
    mpbid
    rexlimiva
    @8
    @1
    @0
    @5
    wb
    2z
    @8
    @1
    wa
    @0
    @2
    c2
    cmul
    co
    #
    cN
    wceq
    #
    vn
    cz
    wrex
    @5
    vn
    c2
    cN
    divides
    @10
    @4
    vn
    cz
    @6
    @9
    @3
    cN
    @6
    @2
    c2
    @2
    zcn
    @6
    2cnd
    mulcomd
    eqeq1d
    rexbiia
    syl6bb
    mpan
    pm5.21nii
end

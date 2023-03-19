include "com.mm"
include "wcel.mm"
include "c0.mm"
include "cfinxp.mm"
include "wceq.mm"
include "cv.mm"
include "csuc.mm"
include "finxpeq2.mm"
include "eqeq1d.mm"
include "finxp0.mm"
include "c1o.mm"
include "suceq.mm"
include "df-1o.mm"
include "syl6eqr.mm"
include "syl.mm"
include "finxp1o.mm"
include "syl6eq.mm"
include "adantl.mm"
include "wne.mm"
include "wa.mm"
include "cxp.mm"
include "finxpsuc.mm"
include "xp0.mm"
include "pm2.61dane.mm"
include "a1d.mm"
include "finds.mm"
include "finxpnom.mm"
include "pm2.61i.mm"

theorem finxp00
  let cN: class N
  let vn: setvar n
  let vm: setvar m


  assert |- ( (/) ^^ N ) = (/)

  proof
    cN
    com
    wcel
    c0
    cN
    cfinxp
    #
    c0
    wceq
    #
    c0
    vn
    cv
    #
    cfinxp
    #
    c0
    wceq
    c0
    c0
    cfinxp
    #
    c0
    wceq
    c0
    vm
    cv
    #
    cfinxp
    #
    c0
    wceq
    #
    c0
    @5
    csuc
    #
    cfinxp
    #
    c0
    wceq
    #
    @1
    vn
    vm
    cN
    @2
    c0
    wceq
    @3
    @4
    c0
    c0
    @2
    c0
    finxpeq2
    eqeq1d
    @2
    @5
    wceq
    @3
    @6
    c0
    c0
    @2
    @5
    finxpeq2
    eqeq1d
    @2
    @8
    wceq
    @3
    @9
    c0
    c0
    @2
    @8
    finxpeq2
    eqeq1d
    @2
    cN
    wceq
    @3
    @0
    c0
    c0
    @2
    cN
    finxpeq2
    eqeq1d
    c0
    finxp0
    @5
    com
    wcel
    #
    @10
    @7
    @11
    @10
    @5
    c0
    @5
    c0
    wceq
    #
    @10
    @11
    @12
    @9
    c0
    c1o
    cfinxp
    #
    c0
    @12
    @8
    c1o
    wceq
    @9
    @13
    wceq
    @12
    @8
    c0
    csuc
    c1o
    @5
    c0
    suceq
    df-1o
    syl6eqr
    c0
    @8
    c1o
    finxpeq2
    syl
    c0
    finxp1o
    syl6eq
    adantl
    @11
    @5
    c0
    wne
    wa
    @9
    @6
    c0
    cxp
    c0
    c0
    @5
    finxpsuc
    @6
    xp0
    syl6eq
    pm2.61dane
    a1d
    finds
    c0
    cN
    finxpnom
    pm2.61i
end

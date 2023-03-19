include "cpgp.mm"
include "wbr.mm"
include "cprime.mm"
include "wcel.mm"
include "cgrp.mm"
include "cv.mm"
include "cod.mm"
include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cn0.mm"
include "wrex.mm"
include "cbs.mm"
include "wral.mm"
include "eqid.mm"
include "ispgp.mm"
include "simp1bi.mm"

theorem pgpprm
  let cP: class P
  let cG: class G
  let vn: setvar n
  let vx: setvar x
  let cN: class N
  let cX: class X


  assert |- ( P pGrp G -> P e. Prime )

  proof
    cP
    cG
    cpgp
    wbr
    cP
    cprime
    wcel
    cG
    cgrp
    wcel
    vx
    cv
    cG
    cod
    cfv
    #
    cfv
    cP
    vn
    cv
    cexp
    co
    wceq
    vn
    cn0
    wrex
    vx
    cG
    cbs
    cfv
    #
    wral
    vx
    cP
    vn
    cG
    @0
    @1
    @1
    eqid
    @0
    eqid
    ispgp
    simp1bi
end

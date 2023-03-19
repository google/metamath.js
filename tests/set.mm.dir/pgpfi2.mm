include "cgrp.mm"
include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "cpgp.mm"
include "wbr.mm"
include "cprime.mm"
include "chash.mm"
include "cfv.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cn0.mm"
include "wrex.mm"
include "cpc.mm"
include "pgpfi.mm"
include "cn.mm"
include "wb.mm"
include "id.mm"
include "c0.mm"
include "wne.mm"
include "grpbn0.mm"
include "hashnncl.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "pcprmpw.mm"
include "syl2anr.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem pgpfi2
  let cP: class P
  let cG: class G
  let cX: class X
  let vg: setvar g
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vx: setvar x
  assume pgpfi.1: |- X = ( Base ` G )


  assert |- ( ( G e. Grp /\ X e. Fin ) -> ( P pGrp G <-> ( P e. Prime /\ ( # ` X ) = ( P ^ ( P pCnt ( # ` X ) ) ) ) ) )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cfn
    wcel
    #
    wa
    #
    cP
    cG
    cpgp
    wbr
    cP
    cprime
    wcel
    #
    cX
    chash
    cfv
    #
    cP
    vn
    cv
    cexp
    co
    wceq
    vn
    cn0
    wrex
    #
    wa
    @3
    @4
    cP
    cP
    @4
    cpc
    co
    cexp
    co
    wceq
    #
    wa
    cP
    vn
    cG
    cX
    pgpfi.1
    pgpfi
    @2
    @3
    @5
    @6
    @3
    @3
    @4
    cn
    wcel
    #
    @5
    @6
    wb
    @2
    @3
    id
    @0
    @1
    @7
    @0
    @7
    @1
    cX
    c0
    wne
    cX
    cG
    pgpfi.1
    grpbn0
    cX
    hashnncl
    syl5ibrcom
    imp
    @4
    cP
    vn
    pcprmpw
    syl2anr
    pm5.32da
    bitrd
end

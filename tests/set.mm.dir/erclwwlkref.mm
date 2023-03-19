include "cv.mm"
include "cclwwlk.mm"
include "cfv.mm"
include "wcel.mm"
include "ccsh.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "wrex.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "anidm.mm"
include "anbi1i.mm"
include "df-3an.mm"
include "cvv.mm"
include "cvtx.mm"
include "cword.mm"
include "c0.mm"
include "wne.mm"
include "eqid.mm"
include "clwwlkbp.mm"
include "cshw0.mm"
include "cn0.mm"
include "cle.mm"
include "0nn0.mm"
include "a1i.mm"
include "lencl.mm"
include "hashge0.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "eqcom.mm"
include "biimpi.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2an.mm"
include "mpdan.mm"
include "3ad2ant2.mm"
include "syl.mm"
include "pm4.71i.mm"
include "3bitr4ri.mm"
include "wb.mm"
include "vex.mm"
include "erclwwlkeq.mm"
include "mp2an.mm"
include "bitr4i.mm"

theorem erclwwlkref
  let vx: setvar x
  let vw: setvar w
  let vu: setvar u
  let c.sm: class .~
  let vn: setvar n
  let cG: class G
  assume erclwwlk.r: |- .~ = { <. u , w >. | ( u e. ( ClWWalks ` G ) /\ w e. ( ClWWalks ` G ) /\ E. n e. ( 0 ... ( # ` w ) ) u = ( w cyclShift n ) ) }

  disjoint G n
  disjoint G u
  disjoint G w
  disjoint n u
  disjoint n w
  disjoint u w
  disjoint n x
  disjoint u x
  disjoint w x
  assert |- ( x e. ( ClWWalks ` G ) <-> x .~ x )

  proof
    vx
    cv
    #
    cG
    cclwwlk
    cfv
    wcel
    #
    @1
    @1
    @0
    @0
    vn
    cv
    #
    ccsh
    co
    #
    wceq
    #
    vn
    cc0
    @0
    chash
    cfv
    #
    cfz
    co
    #
    wrex
    #
    w3a
    #
    @0
    @0
    c.sm
    wbr
    #
    @1
    @1
    wa
    #
    @7
    wa
    @1
    @7
    wa
    @8
    @1
    @10
    @1
    @7
    @1
    anidm
    anbi1i
    @1
    @1
    @7
    df-3an
    @1
    @7
    @1
    cG
    cvv
    wcel
    #
    @0
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    @0
    c0
    wne
    #
    w3a
    @7
    cG
    @12
    @0
    @12
    eqid
    clwwlkbp
    @14
    @11
    @7
    @15
    @14
    @0
    cc0
    ccsh
    co
    #
    @0
    wceq
    #
    @7
    @12
    @0
    cshw0
    @14
    cc0
    @6
    wcel
    #
    @0
    @16
    wceq
    #
    @7
    @17
    @14
    cc0
    cn0
    wcel
    #
    @5
    cn0
    wcel
    cc0
    @5
    cle
    wbr
    @18
    @20
    @14
    0nn0
    a1i
    @12
    @0
    lencl
    @0
    @13
    hashge0
    cc0
    @5
    elfz2nn0
    syl3anbrc
    @17
    @19
    @16
    @0
    eqcom
    biimpi
    @4
    @19
    vn
    cc0
    @6
    @2
    cc0
    wceq
    @3
    @16
    @0
    @2
    cc0
    @0
    ccsh
    oveq2
    eqeq2d
    rspcev
    syl2an
    mpdan
    3ad2ant2
    syl
    pm4.71i
    3bitr4ri
    @0
    cvv
    wcel
    #
    @21
    @9
    @8
    wb
    vx
    vex
    #
    @22
    vw
    vu
    c.sm
    @0
    vn
    cG
    @0
    cvv
    cvv
    erclwwlk.r
    erclwwlkeq
    mp2an
    bitr4i
end

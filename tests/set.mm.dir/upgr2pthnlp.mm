include "cupgr.mm"
include "wcel.mm"
include "cpths.mm"
include "cfv.mm"
include "wbr.mm"
include "c1.mm"
include "chash.mm"
include "clt.mm"
include "w3a.mm"
include "c2.mm"
include "cv.mm"
include "cle.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wral.mm"
include "wceq.mm"
include "2pthnloop.mm"
include "3adant1.mm"
include "wi.mm"
include "cwlks.mm"
include "cdm.mm"
include "cword.mm"
include "pthiswlk.mm"
include "wlkf.mm"
include "simp2.mm"
include "wrdsymbcl.mm"
include "upgrle2.mm"
include "3imp3i2an.mm"
include "wa.mm"
include "cxr.mm"
include "wb.mm"
include "cvv.mm"
include "cxnn0.mm"
include "fvex.mm"
include "hashxnn0.mm"
include "xnn0xr.mm"
include "mp2b.mm"
include "2re.mm"
include "rexri.mm"
include "pm3.2i.mm"
include "xrletri3.mm"
include "mp1i.mm"
include "biimprd.mm"
include "mpand.mm"
include "3exp.mm"
include "3syl.mm"
include "impcom.mm"
include "3adant3.mm"
include "imp.mm"
include "ralimdva.mm"
include "mpd.mm"

theorem upgr2pthnlp
  let cP: class P
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cI: class I
  assume 2pthnloop.i: |- I = ( iEdg ` G )

  disjoint F i
  disjoint G i
  disjoint I i
  disjoint P i
  assert |- ( ( G e. UPGraph /\ F ( Paths ` G ) P /\ 1 < ( # ` F ) ) -> A. i e. ( 0 ..^ ( # ` F ) ) ( # ` ( I ` ( F ` i ) ) ) = 2 )

  proof
    cG
    cupgr
    wcel
    #
    cF
    cP
    cG
    cpths
    cfv
    wbr
    #
    c1
    cF
    chash
    cfv
    #
    clt
    wbr
    #
    w3a
    #
    c2
    vi
    cv
    #
    cF
    cfv
    #
    cI
    cfv
    #
    chash
    cfv
    #
    cle
    wbr
    #
    vi
    cc0
    @2
    cfzo
    co
    #
    wral
    #
    @8
    c2
    wceq
    #
    vi
    @10
    wral
    @1
    @3
    @11
    @0
    cP
    vi
    cF
    cG
    cI
    2pthnloop.i
    2pthnloop
    3adant1
    @4
    @9
    @12
    vi
    @10
    @4
    @5
    @10
    wcel
    #
    @9
    @12
    wi
    #
    @0
    @1
    @13
    @14
    wi
    #
    @3
    @1
    @0
    @15
    @1
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    cF
    cI
    cdm
    #
    cword
    wcel
    #
    @0
    @15
    wi
    cP
    cF
    cG
    pthiswlk
    cP
    cF
    cG
    cI
    2pthnloop.i
    wlkf
    @17
    @0
    @13
    @14
    @17
    @0
    @13
    w3a
    #
    @8
    c2
    cle
    wbr
    #
    @9
    @12
    @17
    @0
    @13
    @0
    @6
    @16
    wcel
    @19
    @17
    @0
    @13
    simp2
    @5
    @16
    cF
    wrdsymbcl
    cG
    cI
    @6
    2pthnloop.i
    upgrle2
    3imp3i2an
    @18
    @12
    @19
    @9
    wa
    #
    @8
    cxr
    wcel
    #
    c2
    cxr
    wcel
    #
    wa
    @12
    @20
    wb
    @18
    @21
    @22
    @7
    cvv
    wcel
    @8
    cxnn0
    wcel
    @21
    @6
    cI
    fvex
    @7
    cvv
    hashxnn0
    @8
    xnn0xr
    mp2b
    c2
    2re
    rexri
    pm3.2i
    @8
    c2
    xrletri3
    mp1i
    biimprd
    mpand
    3exp
    3syl
    impcom
    3adant3
    imp
    ralimdva
    mpd
end

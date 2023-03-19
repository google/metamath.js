include "cm1r.mm"
include "c1p.mm"
include "cop.mm"
include "cer.mm"
include "cec.mm"
include "cltr.mm"
include "wbr.mm"
include "cpp.mm"
include "co.mm"
include "cltp.mm"
include "cplr.mm"
include "cnp.mm"
include "wcel.mm"
include "df-m1r.mm"
include "breq1i.mm"
include "ltsrpr.mm"
include "bitri.mm"
include "cnr.mm"
include "wb.mm"
include "ltasr.mm"
include "ax-mp.mm"
include "ltrelpr.mm"
include "brel.mm"
include "simprd.mm"
include "dmplp.mm"
include "0npr.mm"
include "ndmovrcl.mm"
include "syl.mm"
include "1pr.mm"
include "addclpr.mm"
include "mp2an.mm"
include "ltaddpr.mm"
include "mpan.mm"
include "impbii.mm"
include "3bitr3i.mm"

theorem mappsrpr
  let cA: class A
  let cC: class C
  assume mappsrpr.2: |- C e. R.


  assert |- ( ( C +R -1R ) <R ( C +R [ <. A , 1P >. ] ~R ) <-> A e. P. )

  proof
    cm1r
    cA
    c1p
    cop
    cer
    cec
    #
    cltr
    wbr
    #
    c1p
    c1p
    cpp
    co
    #
    @2
    cA
    cpp
    co
    #
    cltp
    wbr
    #
    cC
    cm1r
    cplr
    co
    cC
    @0
    cplr
    co
    cltr
    wbr
    #
    cA
    cnp
    wcel
    #
    @1
    c1p
    @2
    cop
    cer
    cec
    #
    @0
    cltr
    wbr
    @4
    cm1r
    @7
    @0
    cltr
    df-m1r
    breq1i
    c1p
    @2
    cA
    c1p
    ltsrpr
    bitri
    cC
    cnr
    wcel
    @1
    @5
    wb
    mappsrpr.2
    cm1r
    @0
    cC
    ltasr
    ax-mp
    @4
    @6
    @4
    @3
    cnp
    wcel
    #
    @6
    @4
    @2
    cnp
    wcel
    #
    @8
    @2
    @3
    cnp
    cnp
    cltp
    ltrelpr
    brel
    simprd
    @8
    @9
    @6
    @2
    cA
    cnp
    cpp
    dmplp
    0npr
    ndmovrcl
    simprd
    syl
    @9
    @6
    @4
    c1p
    cnp
    wcel
    #
    @10
    @9
    1pr
    1pr
    c1p
    c1p
    addclpr
    mp2an
    @2
    cA
    ltaddpr
    mpan
    impbii
    3bitr3i
end

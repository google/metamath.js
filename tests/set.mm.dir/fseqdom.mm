include "wcel.mm"
include "com.mm"
include "cv.mm"
include "cmap.mm"
include "co.mm"
include "ciun.mm"
include "cvv.mm"
include "cxp.mm"
include "cdom.mm"
include "wbr.mm"
include "omex.mm"
include "ovex.mm"
include "iunex.mm"
include "c1st.mm"
include "cfv.mm"
include "csuc.mm"
include "c2nd.mm"
include "csn.mm"
include "xp1st.mm"
include "peano2.mm"
include "syl.mm"
include "wa.mm"
include "wf.mm"
include "xp2nd.mm"
include "fconst6g.mm"
include "adantl.mm"
include "wb.mm"
include "elmapg.mm"
include "sylan2.mm"
include "mpbird.mm"
include "oveq2.mm"
include "eliuni.mm"
include "syl2an2.mm"
include "ex.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "c0.mm"
include "wne.mm"
include "nsuceq0.mm"
include "fvex.mm"
include "snnz.mm"
include "xp11.mm"
include "mp2an.mm"
include "peano4.mm"
include "syl2an.mm"
include "sneqbg.mm"
include "mp1i.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "xpopth.mm"
include "bitrd.mm"
include "a1i.mm"
include "dom2d.mm"
include "mpi.mm"

theorem fseqdom
  let cA: class A
  let vn: setvar n
  let cV: class V
  let vx: setvar x
  let vy: setvar y

  disjoint A n
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint V x
  disjoint V y
  assert |- ( A e. V -> ( _om X. A ) ~<_ U_ n e. _om ( A ^m n ) )

  proof
    cA
    cV
    wcel
    #
    vn
    com
    cA
    vn
    cv
    #
    cmap
    co
    #
    ciun
    #
    cvv
    wcel
    com
    cA
    cxp
    #
    @3
    cdom
    wbr
    vn
    com
    @2
    omex
    cA
    @1
    cmap
    ovex
    iunex
    @0
    vx
    vy
    @4
    @3
    vx
    cv
    #
    c1st
    cfv
    #
    csuc
    #
    @5
    c2nd
    cfv
    #
    csn
    #
    cxp
    #
    vy
    cv
    #
    c1st
    cfv
    #
    csuc
    #
    @11
    c2nd
    cfv
    #
    csn
    #
    cxp
    #
    cvv
    @0
    @5
    @4
    wcel
    #
    @10
    @3
    wcel
    #
    @17
    @7
    com
    wcel
    #
    @0
    @10
    cA
    @7
    cmap
    co
    #
    wcel
    #
    @18
    @17
    @6
    com
    wcel
    #
    @19
    @5
    com
    cA
    xp1st
    #
    @6
    peano2
    syl
    #
    @0
    @17
    wa
    @21
    @7
    cA
    @10
    wf
    #
    @17
    @25
    @0
    @17
    @8
    cA
    wcel
    @25
    @5
    com
    cA
    xp2nd
    @7
    @8
    cA
    fconst6g
    syl
    adantl
    @17
    @0
    @19
    @21
    @25
    wb
    @24
    cA
    @7
    @10
    cV
    com
    elmapg
    sylan2
    mpbird
    vn
    @7
    @2
    @20
    com
    @10
    @1
    @7
    cA
    cmap
    oveq2
    eliuni
    syl2an2
    ex
    @17
    @11
    @4
    wcel
    #
    wa
    #
    @10
    @16
    wceq
    #
    vx
    vy
    weq
    #
    wb
    wi
    @0
    @27
    @28
    @6
    @12
    wceq
    #
    @8
    @14
    wceq
    #
    wa
    #
    @29
    @28
    @7
    @13
    wceq
    #
    @9
    @15
    wceq
    #
    wa
    #
    @27
    @32
    @7
    c0
    wne
    @9
    c0
    wne
    @28
    @35
    wb
    @6
    nsuceq0
    @8
    @5
    c2nd
    fvex
    #
    snnz
    @7
    @9
    @13
    @15
    xp11
    mp2an
    @27
    @33
    @30
    @34
    @31
    @17
    @22
    @12
    com
    wcel
    @33
    @30
    wb
    @26
    @23
    @11
    com
    cA
    xp1st
    @6
    @12
    peano4
    syl2an
    @8
    cvv
    wcel
    @34
    @31
    wb
    @27
    @36
    @8
    @14
    cvv
    sneqbg
    mp1i
    anbi12d
    syl5bb
    @5
    @11
    com
    cA
    com
    cA
    xpopth
    bitrd
    a1i
    dom2d
    mpi
end

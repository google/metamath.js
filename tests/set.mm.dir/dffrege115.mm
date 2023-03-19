include "cv.mm"
include "wbr.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "cop.mm"
include "ccnv.mm"
include "wcel.mm"
include "wex.mm"
include "wfun.mm"
include "alcom.mm"
include "wa.mm"
include "wmo.mm"
include "19.21v.mm"
include "impexp.mm"
include "vex.mm"
include "brcnv.mm"
include "df-br.mm"
include "3bitr3ri.mm"
include "anbi12ci.mm"
include "imbi1i.mm"
include "bitr3i.mm"
include "albii.mm"
include "bitri.mm"
include "opeq2.mm"
include "eleq1d.mm"
include "mo4.mm"
include "mo2v.mm"
include "3bitr2i.mm"
include "wrel.mm"
include "relcnv.mm"
include "biantrur.mm"
include "dffun5.mm"
include "bitr4i.mm"
include "3bitri.mm"

theorem dffrege115
  let cR: class R
  let va: setvar a
  let vb: setvar b
  let vc: setvar c

  disjoint a b
  disjoint a c
  disjoint R a
  disjoint b c
  disjoint R b
  disjoint R c
  assert |- ( A. c A. b ( b R c -> A. a ( b R a -> a = c ) ) <-> Fun `' `' R )

  proof
    vb
    cv
    #
    vc
    cv
    #
    cR
    wbr
    #
    @0
    va
    cv
    #
    cR
    wbr
    #
    va
    vc
    weq
    #
    wi
    #
    va
    wal
    wi
    #
    vb
    wal
    vc
    wal
    @7
    vc
    wal
    #
    vb
    wal
    @0
    @3
    cop
    #
    cR
    ccnv
    #
    ccnv
    #
    wcel
    #
    @5
    wi
    va
    wal
    vc
    wex
    #
    vb
    wal
    #
    @11
    wfun
    #
    @7
    vc
    vb
    alcom
    @8
    @13
    vb
    @8
    @12
    @0
    @1
    cop
    #
    @11
    wcel
    #
    wa
    #
    @5
    wi
    #
    vc
    wal
    va
    wal
    #
    @12
    va
    wmo
    @13
    @8
    @19
    va
    wal
    #
    vc
    wal
    @20
    @7
    @21
    vc
    @7
    @2
    @6
    wi
    #
    va
    wal
    @21
    @2
    @6
    va
    19.21v
    @22
    @19
    va
    @22
    @2
    @4
    wa
    #
    @5
    wi
    @19
    @2
    @4
    @5
    impexp
    @23
    @18
    @5
    @2
    @17
    @4
    @12
    @0
    @1
    @11
    wbr
    @1
    @0
    @10
    wbr
    @17
    @2
    @0
    @1
    @10
    vb
    vex
    #
    vc
    vex
    #
    brcnv
    @0
    @1
    @11
    df-br
    @1
    @0
    cR
    @25
    @24
    brcnv
    3bitr3ri
    @0
    @3
    @11
    wbr
    @3
    @0
    @10
    wbr
    @12
    @4
    @0
    @3
    @10
    @24
    va
    vex
    #
    brcnv
    @0
    @3
    @11
    df-br
    @3
    @0
    cR
    @26
    @24
    brcnv
    3bitr3ri
    anbi12ci
    imbi1i
    bitr3i
    albii
    bitr3i
    albii
    @19
    vc
    va
    alcom
    bitri
    @12
    @17
    va
    vc
    @5
    @9
    @16
    @11
    @3
    @1
    @0
    opeq2
    eleq1d
    mo4
    @12
    va
    vc
    mo2v
    3bitr2i
    albii
    @14
    @11
    wrel
    #
    @14
    wa
    @15
    @27
    @14
    @10
    relcnv
    biantrur
    vb
    va
    vc
    @11
    dffun5
    bitr4i
    3bitri
end

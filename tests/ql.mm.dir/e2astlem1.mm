include "wo.mm"
include "wa.mm"
include "anandir.mm"
include "leo.mm"
include "ler.mm"
include "lecom.mm"
include "wn.mm"
include "comcom7.mm"
include "fh2r.mm"
include "df2le2.mm"
include "wf.mm"
include "ax-a3.mm"
include "lan.mm"
include "comcom.mm"
include "com2or.mm"
include "fh2.mm"
include "lecon3.mm"
include "ortha.mm"
include "ax-r5.mm"
include "ax-r2.mm"
include "or0r.mm"
include "3tr.mm"
include "2or.mm"
include "leor.mm"
include "or32.mm"
include "fh2c.mm"
include "lor.mm"
include "or0.mm"
include "2an.mm"

theorem e2astlem1
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  let wvr: term r
  assume e2ast.1: |- a =< b '
  assume e2ast.2: |- c =< d '
  assume e2ast.3: |- r =< a '
  assume e2ast.4: |- a =< c '
  assume e2ast.5: |- c =< r '


  assert |- ( ( ( a v b ) ^ ( c v d ) ) ^ ( ( a v c ) v r ) ) = ( ( a v ( b ^ ( c v r ) ) ) ^ ( c v ( d ^ ( a v r ) ) ) )

  proof
    wva
    wvb
    wo
    #
    wvc
    wvd
    wo
    #
    wa
    wva
    wvc
    wo
    #
    wvr
    wo
    #
    wa
    @0
    @3
    wa
    #
    @1
    @3
    wa
    #
    wa
    wva
    wvb
    wvc
    wvr
    wo
    #
    wa
    #
    wo
    #
    wvc
    wvd
    wva
    wvr
    wo
    #
    wa
    #
    wo
    #
    wa
    @0
    @1
    @3
    anandir
    @4
    @8
    @5
    @11
    @4
    wva
    @3
    wa
    #
    wvb
    @3
    wa
    #
    wo
    @8
    wva
    @3
    wvb
    wva
    @3
    wva
    @2
    wvr
    wva
    wvc
    leo
    ler
    #
    lecom
    wva
    wvb
    wva
    wvb
    wn
    e2ast.1
    lecom
    comcom7
    #
    fh2r
    @12
    wva
    @13
    @7
    wva
    @3
    @14
    df2le2
    @13
    wvb
    wva
    @6
    wo
    #
    wa
    #
    wf
    @7
    wo
    #
    @7
    @3
    @16
    wvb
    wva
    wvc
    wvr
    ax-a3
    lan
    @17
    wvb
    wva
    wa
    #
    @7
    wo
    @18
    wva
    wvb
    @6
    @15
    wva
    wvc
    wvr
    wva
    wvc
    wva
    wvc
    wn
    e2ast.4
    lecom
    comcom7
    #
    wvr
    wva
    wvr
    wva
    wvr
    wva
    wn
    e2ast.3
    lecom
    comcom7
    comcom
    com2or
    fh2
    @19
    wf
    @7
    wvb
    wva
    wva
    wvb
    e2ast.1
    lecon3
    ortha
    ax-r5
    ax-r2
    @7
    or0r
    3tr
    2or
    ax-r2
    @5
    wvc
    @3
    wa
    #
    wvd
    @3
    wa
    #
    wo
    @11
    wvc
    @3
    wvd
    wvc
    @3
    wvc
    @2
    wvr
    wvc
    wva
    leor
    ler
    #
    lecom
    wvc
    wvd
    wvc
    wvd
    wn
    e2ast.2
    lecom
    comcom7
    #
    fh2r
    @21
    wvc
    @22
    @10
    wvc
    @3
    @23
    df2le2
    @22
    wvd
    @9
    wvc
    wo
    #
    wa
    @10
    wvd
    wvc
    wa
    #
    wo
    #
    @10
    @3
    @25
    wvd
    wva
    wvc
    wvr
    or32
    lan
    wvc
    wvd
    @9
    @24
    wvc
    wva
    wvr
    wva
    wvc
    @20
    comcom
    wvc
    wvr
    wvc
    wvr
    wn
    e2ast.5
    lecom
    comcom7
    com2or
    fh2c
    @27
    @10
    wf
    wo
    @10
    @26
    wf
    @10
    wvd
    wvc
    wvc
    wvd
    e2ast.2
    lecon3
    ortha
    lor
    @10
    or0
    ax-r2
    3tr
    2or
    ax-r2
    2an
    ax-r2
end

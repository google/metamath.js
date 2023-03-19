include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "csn.mm"
include "cdif.mm"
include "cun.mm"
include "fzsuc.mm"
include "difeq1d.mm"
include "wceq.mm"
include "uncom.mm"
include "wss.mm"
include "cin.mm"
include "c0.mm"
include "wb.mm"
include "ssun2.mm"
include "incom.mm"
include "fzp1disj.mm"
include "eqtri.mm"
include "a1i.mm"
include "uneqdifeq.mm"
include "sylancr.mm"
include "mpbii.mm"
include "eqtr2d.mm"

theorem fzdifsuc
  let cM: class M
  let cN: class N


  assert |- ( N e. ( ZZ>= ` M ) -> ( M ... N ) = ( ( M ... ( N + 1 ) ) \ { ( N + 1 ) } ) )

  proof
    cN
    cM
    cuz
    cfv
    wcel
    #
    cM
    cN
    c1
    caddc
    co
    #
    cfz
    co
    #
    @1
    csn
    #
    cdif
    cM
    cN
    cfz
    co
    #
    @3
    cun
    #
    @3
    cdif
    #
    @4
    @0
    @2
    @5
    @3
    cM
    cN
    fzsuc
    difeq1d
    @0
    @3
    @4
    cun
    @5
    wceq
    #
    @6
    @4
    wceq
    #
    @3
    @4
    uncom
    @0
    @3
    @5
    wss
    @3
    @4
    cin
    #
    c0
    wceq
    #
    @7
    @8
    wb
    @3
    @4
    ssun2
    @10
    @0
    @9
    @4
    @3
    cin
    c0
    @3
    @4
    incom
    cM
    cN
    fzp1disj
    eqtri
    a1i
    @3
    @4
    @5
    uneqdifeq
    sylancr
    mpbii
    eqtr2d
end

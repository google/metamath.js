include "cdvds.mm"
include "csn.mm"
include "cima.mm"
include "cn.mm"
include "cin.mm"
include "cabs.mm"
include "cfv.mm"
include "cuz.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "crab.mm"
include "cab.mm"
include "wrel.mm"
include "wceq.mm"
include "reldvds.mm"
include "relimasn.mm"
include "ax-mp.mm"
include "ineq1i.mm"
include "dfrab2.mm"
include "eqtr4i.mm"
include "eleq2i.mm"
include "wa.mm"
include "cle.mm"
include "rabid.mm"
include "cz.mm"
include "wb.mm"
include "nnz.mm"
include "absdvdsb.mm"
include "syl2an.mm"
include "wi.mm"
include "zabscl.mm"
include "syl.mm"
include "dvdsle.mm"
include "sylan.mm"
include "sylbid.mm"
include "impr.mm"
include "sylan2b.mm"
include "simplbi.mm"
include "nnzd.mm"
include "eluz.mm"
include "mpbird.mm"
include "ex.mm"
include "ssrdv.mm"

theorem nznngen
  let wph: wff ph
  let cN: class N
  let vx: setvar x
  assume nznngen.n: |- ( ph -> N e. ZZ )


  assert |- ( ph -> ( ( || " { N } ) i^i NN ) C_ ( ZZ>= ` ( abs ` N ) ) )

  proof
    wph
    vx
    cdvds
    cN
    csn
    cima
    #
    cn
    cin
    #
    cN
    cabs
    cfv
    #
    cuz
    cfv
    #
    wph
    vx
    cv
    #
    @1
    wcel
    #
    @4
    @3
    wcel
    #
    @5
    wph
    @4
    cN
    @4
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    wcel
    #
    @6
    @1
    @8
    @4
    @1
    @7
    vx
    cab
    #
    cn
    cin
    @8
    @0
    @10
    cn
    cdvds
    wrel
    @0
    @10
    wceq
    reldvds
    vx
    cN
    cdvds
    relimasn
    ax-mp
    ineq1i
    @7
    vx
    cn
    dfrab2
    eqtr4i
    eleq2i
    wph
    @9
    wa
    @6
    @2
    @4
    cle
    wbr
    #
    @9
    wph
    @4
    cn
    wcel
    #
    @7
    wa
    @11
    @7
    vx
    cn
    rabid
    #
    wph
    @12
    @7
    @11
    wph
    @12
    wa
    @7
    @2
    @4
    cdvds
    wbr
    #
    @11
    wph
    cN
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    @7
    @14
    wb
    @12
    nznngen.n
    @4
    nnz
    cN
    @4
    absdvdsb
    syl2an
    wph
    @2
    cz
    wcel
    #
    @12
    @14
    @11
    wi
    wph
    @15
    @17
    nznngen.n
    cN
    zabscl
    syl
    #
    @2
    @4
    dvdsle
    sylan
    sylbid
    impr
    sylan2b
    wph
    @17
    @16
    @6
    @11
    wb
    @9
    @18
    @9
    @4
    @9
    @12
    @7
    @13
    simplbi
    nnzd
    @2
    @4
    eluz
    syl2an
    mpbird
    sylan2b
    ex
    ssrdv
end

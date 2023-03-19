include "cofld.mm"
include "wcel.mm"
include "wbr.mm"
include "cple.mm"
include "cfv.mm"
include "wne.mm"
include "corng.mm"
include "cfield.mm"
include "isofld.mm"
include "simprbi.mm"
include "eqid.mm"
include "orng0le1.mm"
include "syl.mm"
include "cdr.mm"
include "ofldfld.mm"
include "ccrg.mm"
include "isfld.mm"
include "simplbi.mm"
include "drngunz.mm"
include "3syl.mm"
include "necomd.mm"
include "cvv.mm"
include "wa.mm"
include "wb.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cur.mm"
include "pltval.mm"
include "mp3an23.mm"
include "mpbir2and.mm"

theorem ofldlt1
  let c.lt: class .<
  let c.1: class .1.
  let cF: class F
  let c.0: class .0.
  assume orng0le1.1: |- .0. = ( 0g ` F )
  assume orng0le1.2: |- .1. = ( 1r ` F )
  assume ofld0lt1.3: |- .< = ( lt ` F )


  assert |- ( F e. oField -> .0. .< .1. )

  proof
    cF
    cofld
    wcel
    #
    c.0
    c.1
    c.lt
    wbr
    #
    c.0
    c.1
    cF
    cple
    cfv
    #
    wbr
    #
    c.0
    c.1
    wne
    #
    @0
    cF
    corng
    wcel
    #
    @3
    @0
    cF
    cfield
    wcel
    #
    @5
    cF
    isofld
    simprbi
    c.1
    cF
    @2
    c.0
    orng0le1.1
    orng0le1.2
    @2
    eqid
    #
    orng0le1
    syl
    @0
    c.1
    c.0
    @0
    @6
    cF
    cdr
    wcel
    #
    c.1
    c.0
    wne
    cF
    ofldfld
    @6
    @8
    cF
    ccrg
    wcel
    cF
    isfld
    simplbi
    cF
    c.1
    c.0
    orng0le1.1
    orng0le1.2
    drngunz
    3syl
    necomd
    @0
    c.0
    cvv
    wcel
    c.1
    cvv
    wcel
    @1
    @3
    @4
    wa
    wb
    c.0
    cF
    c0g
    cfv
    cvv
    orng0le1.1
    cF
    c0g
    fvex
    eqeltri
    c.1
    cF
    cur
    cfv
    cvv
    orng0le1.2
    cF
    cur
    fvex
    eqeltri
    cofld
    cvv
    cvv
    c.lt
    cF
    @2
    c.0
    c.1
    @7
    ofld0lt1.3
    pltval
    mp3an23
    mpbir2and
end

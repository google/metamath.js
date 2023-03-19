include "cdrng.mm"
include "wcel.mm"
include "cop.mm"
include "csn.mm"
include "wn.mm"
include "wne.mm"
include "cgi.mm"
include "cfv.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "zrdivrng.mm"
include "wceq.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "crngo.mm"
include "wb.mm"
include "cdif.mm"
include "cxp.mm"
include "cres.mm"
include "cgr.mm"
include "drngoi.mm"
include "simpld.mm"
include "rngoueqz.mm"
include "syl.mm"
include "wi.mm"
include "rngosn6.mm"
include "eleq1.mm"
include "biimpd.mm"
include "syl6bi.mm"
include "pm2.43a.mm"
include "sylbird.mm"
include "necon3bd.mm"
include "mpi.mm"

theorem dvrunz
  let cR: class R
  let cU: class U
  let cG: class G
  let cH: class H
  let cX: class X
  let cZ: class Z
  assume dvrunz.1: |- G = ( 1st ` R )
  assume dvrunz.2: |- H = ( 2nd ` R )
  assume dvrunz.3: |- X = ran G
  assume dvrunz.4: |- Z = ( GId ` G )
  assume dvrunz.5: |- U = ( GId ` H )


  assert |- ( R e. DivRingOps -> U =/= Z )

  proof
    cR
    cdrng
    wcel
    #
    cZ
    cZ
    cop
    cZ
    cop
    csn
    #
    @1
    cop
    #
    cdrng
    wcel
    #
    wn
    cU
    cZ
    wne
    cZ
    cZ
    cG
    cgi
    cfv
    cvv
    dvrunz.4
    cG
    cgi
    fvex
    eqeltri
    zrdivrng
    @0
    @3
    cU
    cZ
    @0
    cU
    cZ
    wceq
    #
    cX
    c1o
    cen
    wbr
    #
    @3
    @0
    cR
    crngo
    wcel
    #
    @5
    @4
    wb
    @0
    @6
    cH
    cX
    cZ
    csn
    cdif
    #
    @7
    cxp
    cres
    cgr
    wcel
    cR
    cG
    cH
    cX
    cZ
    dvrunz.1
    dvrunz.2
    dvrunz.3
    dvrunz.4
    drngoi
    simpld
    #
    cR
    cU
    cG
    cH
    cX
    cZ
    dvrunz.1
    dvrunz.2
    dvrunz.4
    dvrunz.5
    dvrunz.3
    rngoueqz
    syl
    @5
    @0
    @3
    @0
    @5
    cR
    @2
    wceq
    #
    @0
    @3
    wi
    @0
    @6
    @5
    @9
    wb
    @8
    cR
    cG
    cX
    cZ
    dvrunz.1
    dvrunz.3
    dvrunz.4
    rngosn6
    syl
    @9
    @0
    @3
    cR
    @2
    cdrng
    eleq1
    biimpd
    syl6bi
    pm2.43a
    sylbird
    necon3bd
    mpi
end

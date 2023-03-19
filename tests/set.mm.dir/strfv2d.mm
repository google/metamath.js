include "cfv.mm"
include "cnx.mm"
include "strfvnd.mm"
include "ccnv.mm"
include "cvv.mm"
include "cres.mm"
include "cnvcnv2.mm"
include "fveq1i.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "fvres.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "wfun.mm"
include "cop.mm"
include "cxp.mm"
include "cin.mm"
include "elex.mm"
include "syl.mm"
include "opelxpi.mm"
include "sylancr.mm"
include "elind.mm"
include "cnvcnv.mm"
include "syl6eleqr.mm"
include "funopfv.mm"
include "sylc.mm"
include "syl5eqr.mm"
include "eqtr2d.mm"

theorem strfv2d
  let wph: wff ph
  let cC: class C
  let cS: class S
  let cE: class E
  let cV: class V
  let cW: class W
  assume strfv2d.e: |- E = Slot ( E ` ndx )
  assume strfv2d.s: |- ( ph -> S e. V )
  assume strfv2d.f: |- ( ph -> Fun `' `' S )
  assume strfv2d.n: |- ( ph -> <. ( E ` ndx ) , C >. e. S )
  assume strfv2d.c: |- ( ph -> C e. W )


  assert |- ( ph -> C = ( E ` S ) )

  proof
    wph
    cS
    cE
    cfv
    cnx
    cE
    cfv
    #
    cS
    cfv
    #
    cC
    wph
    cS
    cE
    @0
    cV
    strfv2d.e
    strfv2d.s
    strfvnd
    wph
    @1
    @0
    cS
    ccnv
    ccnv
    #
    cfv
    #
    cC
    @3
    @0
    cS
    cvv
    cres
    #
    cfv
    #
    @1
    @0
    @2
    @4
    cS
    cnvcnv2
    fveq1i
    @0
    cvv
    wcel
    #
    @5
    @1
    wceq
    cnx
    cE
    fvex
    #
    @0
    cvv
    cS
    fvres
    ax-mp
    eqtri
    wph
    @2
    wfun
    @0
    cC
    cop
    #
    @2
    wcel
    @3
    cC
    wceq
    strfv2d.f
    wph
    @8
    cS
    cvv
    cvv
    cxp
    #
    cin
    @2
    wph
    cS
    @9
    @8
    strfv2d.n
    wph
    @6
    cC
    cvv
    wcel
    #
    @8
    @9
    wcel
    @7
    wph
    cC
    cW
    wcel
    @10
    strfv2d.c
    cC
    cW
    elex
    syl
    @0
    cC
    cvv
    cvv
    opelxpi
    sylancr
    elind
    cS
    cnvcnv
    syl6eleqr
    @0
    cC
    @2
    funopfv
    sylc
    syl5eqr
    eqtr2d
end

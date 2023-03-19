include "cdr.mm"
include "wcel.mm"
include "cchr.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "ccnv.mm"
include "cui.mm"
include "cima.mm"
include "c0g.mm"
include "csn.mm"
include "cdif.mm"
include "cz.mm"
include "crg.mm"
include "eqid.mm"
include "isdrng.mm"
include "simprbi.mm"
include "imaeq2d.mm"
include "adantr.mm"
include "wfun.mm"
include "drngring.mm"
include "zring.mm"
include "crh.mm"
include "co.mm"
include "wf.mm"
include "zrhrhm.mm"
include "zringbas.mm"
include "rhmf.mm"
include "ffun.mm"
include "3syl.mm"
include "difpreima.mm"
include "fimacnv.mm"
include "4syl.mm"
include "zrhker.mm"
include "biimpa.mm"
include "sylan.mm"
include "difeq12d.mm"
include "3eqtrd.mm"

theorem zrhunitpreima
  let cB: class B
  let cR: class R
  let cL: class L
  let c.0: class .0.
  let vx: setvar x
  assume zrhker.0: |- B = ( Base ` R )
  assume zrhker.1: |- L = ( ZRHom ` R )
  assume zrhker.2: |- .0. = ( 0g ` R )


  assert |- ( ( R e. DivRing /\ ( chr ` R ) = 0 ) -> ( `' L " ( Unit ` R ) ) = ( ZZ \ { 0 } ) )

  proof
    cR
    cdr
    wcel
    #
    cR
    cchr
    cfv
    cc0
    wceq
    #
    wa
    #
    cL
    ccnv
    #
    cR
    cui
    cfv
    #
    cima
    #
    @3
    cB
    cR
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    cima
    #
    @3
    cB
    cima
    #
    @3
    @7
    cima
    #
    cdif
    #
    cz
    cc0
    csn
    #
    cdif
    @0
    @5
    @9
    wceq
    @1
    @0
    @4
    @8
    @3
    @0
    cR
    crg
    wcel
    #
    @4
    @8
    wceq
    cB
    cR
    @4
    @6
    zrhker.0
    @4
    eqid
    @6
    eqid
    #
    isdrng
    simprbi
    imaeq2d
    adantr
    @0
    @9
    @12
    wceq
    #
    @1
    @0
    @14
    cL
    wfun
    #
    @16
    cR
    drngring
    #
    @14
    cL
    zring
    cR
    crh
    co
    wcel
    #
    cz
    cB
    cL
    wf
    #
    @17
    cR
    cL
    zrhker.1
    zrhrhm
    #
    cz
    cB
    zring
    cR
    cL
    zringbas
    zrhker.0
    rhmf
    #
    cz
    cB
    cL
    ffun
    3syl
    cB
    @7
    cL
    difpreima
    3syl
    adantr
    @2
    @10
    cz
    @11
    @13
    @0
    @10
    cz
    wceq
    #
    @1
    @0
    @14
    @19
    @20
    @23
    @18
    @21
    @22
    cz
    cB
    cL
    fimacnv
    4syl
    adantr
    @0
    @14
    @1
    @11
    @13
    wceq
    #
    @18
    @14
    @1
    @24
    cB
    cR
    cL
    @6
    zrhker.0
    zrhker.1
    @15
    zrhker
    biimpa
    sylan
    difeq12d
    3eqtrd
end

include "cnx.mm"
include "cedgf.mm"
include "cfv.mm"
include "cid.mm"
include "cres.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cusgr.mm"
include "cbs.mm"
include "cvv.mm"
include "eqid.mm"
include "wcel.mm"
include "fvex.mm"
include "cusgrexilem1.mm"
include "mp1i.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "wf1.mm"
include "usgrexilem.mm"
include "usgrstrrepe.mm"
include "syl5eqel.mm"

theorem structtousgr
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cS: class S
  let cG: class G
  let cX: class X
  assume structtousgr.p: |- P = { x e. ~P ( Base ` S ) | ( # ` x ) = 2 }
  assume structtousgr.s: |- ( ph -> S Struct X )
  assume structtousgr.g: |- G = ( S sSet <. ( .ef ` ndx ) , ( _I |` P ) >. )
  assume structtousgr.b: |- ( ph -> ( Base ` ndx ) e. dom S )

  disjoint G x
  disjoint P x
  disjoint S x
  disjoint ph x
  assert |- ( ph -> G e. USGraph )

  proof
    wph
    cG
    cS
    cnx
    cedgf
    cfv
    #
    cid
    cP
    cres
    #
    cop
    csts
    co
    cusgr
    structtousgr.g
    wph
    vx
    @1
    cS
    @0
    cS
    cbs
    cfv
    #
    cvv
    cX
    @2
    eqid
    @0
    eqid
    structtousgr.s
    structtousgr.b
    @2
    cvv
    wcel
    #
    @1
    cvv
    wcel
    wph
    cS
    cbs
    fvex
    #
    vx
    cP
    @2
    cvv
    structtousgr.p
    cusgrexilem1
    mp1i
    @3
    @1
    cdm
    vx
    cv
    chash
    cfv
    c2
    wceq
    vx
    @2
    cpw
    crab
    @1
    wf1
    wph
    @4
    vx
    cP
    @2
    cvv
    structtousgr.p
    usgrexilem
    mp1i
    usgrstrrepe
    syl5eqel
end

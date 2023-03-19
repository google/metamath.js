include "ccrg.mm"
include "wcel.mm"
include "c1o.mm"
include "cmap.mm"
include "co.mm"
include "cpws.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "ccom.mm"
include "crh.mm"
include "cvv.mm"
include "wceq.mm"
include "ovex.mm"
include "eqid.mm"
include "pwsbas.mm"
include "mpan2.mm"
include "mpteq1d.mm"
include "syl5eq.mm"
include "crngring.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "wf1o.mm"
include "wf.mm"
include "c0.mm"
include "df1o2.mm"
include "0ex.mm"
include "mapsnf1o3.mm"
include "f1of.mm"
include "mp1i.mm"
include "pwsco1rhm.mm"
include "eqeltrd.mm"

theorem evls1rhmlem
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let cT: class T
  let cF: class F
  assume evl1rhmlem.b: |- B = ( Base ` R )
  assume evl1rhmlem.t: |- T = ( R ^s B )
  assume evl1rhmlem.f: |- F = ( x e. ( B ^m ( B ^m 1o ) ) |-> ( x o. ( y e. B |-> ( 1o X. { y } ) ) ) )

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint R x
  disjoint T x
  assert |- ( R e. CRing -> F e. ( ( R ^s ( B ^m 1o ) ) RingHom T ) )

  proof
    cR
    ccrg
    wcel
    #
    cF
    vx
    cR
    cB
    c1o
    cmap
    co
    #
    cpws
    co
    #
    cbs
    cfv
    #
    vx
    cv
    vy
    cB
    c1o
    vy
    cv
    csn
    cxp
    cmpt
    #
    ccom
    #
    cmpt
    #
    @2
    cT
    crh
    co
    @0
    cF
    vx
    cB
    @1
    cmap
    co
    #
    @5
    cmpt
    @6
    evl1rhmlem.f
    @0
    vx
    @7
    @3
    @5
    @0
    @1
    cvv
    wcel
    #
    @7
    @3
    wceq
    cB
    c1o
    cmap
    ovex
    #
    cB
    cR
    @1
    ccrg
    cvv
    @2
    @2
    eqid
    #
    evl1rhmlem.b
    pwsbas
    mpan2
    mpteq1d
    syl5eq
    @0
    cB
    @1
    @3
    cR
    vx
    @4
    cvv
    cvv
    cT
    @2
    evl1rhmlem.t
    @10
    @3
    eqid
    cR
    crngring
    cB
    cvv
    wcel
    @0
    cB
    cR
    cbs
    cfv
    cvv
    evl1rhmlem.b
    cR
    cbs
    fvex
    eqeltri
    #
    a1i
    @8
    @0
    @9
    a1i
    cB
    @1
    @4
    wf1o
    cB
    @1
    @4
    wf
    @0
    vy
    cB
    c1o
    @4
    c0
    df1o2
    @11
    0ex
    @4
    eqid
    mapsnf1o3
    cB
    @1
    @4
    f1of
    mp1i
    pwsco1rhm
    eqeltrd
end

include "cii.mm"
include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "cv.mm"
include "c2.mm"
include "cdiv.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "cmul.mm"
include "cif.mm"
include "cfv.mm"
include "cmpt2.mm"
include "cpco.mm"
include "cphtpy.mm"
include "cphtpc.mm"
include "eqid.mm"
include "pcorevlem.mm"
include "simprd.mm"

theorem pcorev
  let vx: setvar x
  let cP: class P
  let cF: class F
  let cG: class G
  let cJ: class J
  let vs: setvar s
  let vt: setvar t
  let vy: setvar y
  let cH: class H
  assume pcorev.1: |- G = ( x e. ( 0 [,] 1 ) |-> ( F ` ( 1 - x ) ) )
  assume pcorev.2: |- P = ( ( 0 [,] 1 ) X. { ( F ` 1 ) } )

  disjoint F x
  disjoint J x
  disjoint P x
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint F s
  disjoint t x
  disjoint t y
  disjoint F t
  disjoint x y
  disjoint F y
  disjoint G s
  disjoint G t
  disjoint G y
  disjoint H y
  disjoint J s
  disjoint J t
  disjoint J y
  disjoint P s
  disjoint P t
  disjoint P y
  assert |- ( F e. ( II Cn J ) -> ( G ( *p ` J ) F ) ( ~=ph ` J ) P )

  proof
    cF
    cii
    cJ
    ccn
    co
    wcel
    vs
    vt
    cc0
    c1
    cicc
    co
    #
    @0
    vs
    cv
    #
    c1
    c2
    cdiv
    co
    cle
    wbr
    c1
    c1
    vt
    cv
    cmin
    co
    #
    c2
    @1
    cmul
    co
    #
    cmul
    co
    cmin
    co
    c1
    @2
    c1
    @3
    c1
    cmin
    co
    cmin
    co
    cmul
    co
    cmin
    co
    cif
    cF
    cfv
    cmpt2
    #
    cG
    cF
    cJ
    cpco
    cfv
    co
    #
    cP
    cJ
    cphtpy
    cfv
    co
    wcel
    @5
    cP
    cJ
    cphtpc
    cfv
    wbr
    vx
    vt
    cP
    cF
    cG
    @4
    cJ
    vs
    pcorev.1
    pcorev.2
    @4
    eqid
    pcorevlem
    simprd
end

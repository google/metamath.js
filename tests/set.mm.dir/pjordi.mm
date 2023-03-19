include "cc0.mm"
include "cv.mm"
include "cpjh.mm"
include "cfv.mm"
include "chod.mm"
include "co.mm"
include "csp.mm"
include "cle.mm"
include "wbr.mm"
include "chil.mm"
include "wral.mm"
include "wss.mm"
include "cima.mm"
include "pjssposi.mm"
include "wfo.mm"
include "wceq.mm"
include "pjfoi.mm"
include "foima.mm"
include "ax-mp.mm"
include "sseq12i.mm"
include "bitr4i.mm"

theorem pjordi
  let vx: setvar x
  let cG: class G
  let cH: class H
  let vy: setvar y
  assume pjco.1: |- G e. CH
  assume pjco.2: |- H e. CH

  disjoint H x
  disjoint G x
  disjoint x y
  disjoint H y
  disjoint G y
  assert |- ( A. x e. ~H 0 <_ ( ( ( ( projh ` H ) -op ( projh ` G ) ) ` x ) .ih x ) <-> ( ( projh ` G ) " ~H ) C_ ( ( projh ` H ) " ~H ) )

  proof
    cc0
    vx
    cv
    #
    cH
    cpjh
    cfv
    #
    cG
    cpjh
    cfv
    #
    chod
    co
    cfv
    @0
    csp
    co
    cle
    wbr
    vx
    chil
    wral
    cG
    cH
    wss
    @2
    chil
    cima
    #
    @1
    chil
    cima
    #
    wss
    vx
    cG
    cH
    pjco.1
    pjco.2
    pjssposi
    @3
    cG
    @4
    cH
    chil
    cG
    @2
    wfo
    @3
    cG
    wceq
    cG
    pjco.1
    pjfoi
    chil
    cG
    @2
    foima
    ax-mp
    chil
    cH
    @1
    wfo
    @4
    cH
    wceq
    cH
    pjco.2
    pjfoi
    chil
    cH
    @1
    foima
    ax-mp
    sseq12i
    bitr4i
end

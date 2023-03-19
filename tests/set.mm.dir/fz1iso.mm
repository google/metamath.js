include "cn.mm"
include "clt.mm"
include "ccnv.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "com.mm"
include "cvv.mm"
include "cv.mm"
include "cmpt.mm"
include "crdg.mm"
include "cres.mm"
include "coi.mm"
include "eqid.mm"
include "fz1isolem.mm"

theorem fz1iso
  let cA: class A
  let cR: class R
  let vf: setvar f
  let vn: setvar n

  disjoint A f
  disjoint R f
  disjoint f n
  disjoint A n
  disjoint R n
  assert |- ( ( R Or A /\ A e. Fin ) -> E. f f Isom < , R ( ( 1 ... ( # ` A ) ) , A ) )

  proof
    cA
    cn
    clt
    ccnv
    cA
    chash
    cfv
    c1
    caddc
    co
    #
    csn
    cima
    cin
    #
    com
    @0
    vn
    cvv
    vn
    cv
    c1
    caddc
    co
    cmpt
    c1
    crdg
    com
    cres
    #
    ccnv
    cfv
    cin
    #
    cR
    vf
    vn
    @2
    cA
    cR
    coi
    #
    @2
    eqid
    @1
    eqid
    @3
    eqid
    @4
    eqid
    fz1isolem
end

include "cdioph.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "cv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cres.mm"
include "wceq.mm"
include "cc0.mm"
include "wa.mm"
include "cn.mm"
include "cmap.mm"
include "wrex.mm"
include "cab.mm"
include "cmzp.mm"
include "eldiophelnn0.mm"
include "cvv.mm"
include "wb.mm"
include "nnex.mm"
include "cfn.mm"
include "wn.mm"
include "wss.mm"
include "cz.mm"
include "1z.mm"
include "nnuz.mm"
include "uzinf.mm"
include "ax-mp.mm"
include "elfznn.mm"
include "ssriv.mm"
include "eldioph2b.mm"
include "mpanr12.mm"
include "mpan2.mm"
include "biadan2.mm"

theorem eldioph3b
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cN: class N
  let vp: setvar p

  disjoint A p
  disjoint A t
  disjoint A u
  disjoint p t
  disjoint p u
  disjoint t u
  disjoint N p
  disjoint N t
  disjoint N u
  assert |- ( A e. ( Dioph ` N ) <-> ( N e. NN0 /\ E. p e. ( mzPoly ` NN ) A = { t | E. u e. ( NN0 ^m NN ) ( t = ( u |` ( 1 ... N ) ) /\ ( p ` u ) = 0 ) } ) )

  proof
    cA
    cN
    cdioph
    cfv
    wcel
    #
    cN
    cn0
    wcel
    #
    cA
    vt
    cv
    vu
    cv
    #
    c1
    cN
    cfz
    co
    #
    cres
    wceq
    @2
    vp
    cv
    #
    cfv
    cc0
    wceq
    wa
    vu
    cn0
    cn
    cmap
    co
    wrex
    vt
    cab
    wceq
    vp
    cn
    cmzp
    cfv
    wrex
    #
    cA
    cN
    eldiophelnn0
    @1
    cn
    cvv
    wcel
    #
    @0
    @5
    wb
    #
    nnex
    @1
    @6
    wa
    cn
    cfn
    wcel
    wn
    #
    @3
    cn
    wss
    @7
    c1
    cz
    wcel
    @8
    1z
    c1
    cn
    nnuz
    uzinf
    ax-mp
    vp
    @3
    cn
    @4
    cN
    elfznn
    ssriv
    vu
    vt
    cA
    cn
    cN
    vp
    eldioph2b
    mpanr12
    mpan2
    biadan2
end

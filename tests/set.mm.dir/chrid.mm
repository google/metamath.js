include "crg.mm"
include "wcel.mm"
include "cfv.mm"
include "cur.mm"
include "cmg.mm"
include "co.mm"
include "cz.mm"
include "wceq.mm"
include "chrcl.mm"
include "nn0zd.mm"
include "eqid.mm"
include "zrhmulg.mm"
include "mpdan.mm"
include "cod.mm"
include "chrval.mm"
include "oveq1i.mm"
include "cbs.mm"
include "ringidcl.mm"
include "odid.mm"
include "syl.mm"
include "syl5eqr.mm"
include "eqtrd.mm"

theorem chrid
  let cC: class C
  let cR: class R
  let cL: class L
  let c.0: class .0.
  assume chrcl.c: |- C = ( chr ` R )
  assume chrid.l: |- L = ( ZRHom ` R )
  assume chrid.z: |- .0. = ( 0g ` R )


  assert |- ( R e. Ring -> ( L ` C ) = .0. )

  proof
    cR
    crg
    wcel
    #
    cC
    cL
    cfv
    #
    cC
    cR
    cur
    cfv
    #
    cR
    cmg
    cfv
    #
    co
    #
    c.0
    @0
    cC
    cz
    wcel
    @1
    @4
    wceq
    @0
    cC
    cC
    cR
    chrcl.c
    chrcl
    nn0zd
    cR
    @3
    @2
    cL
    cC
    chrid.l
    @3
    eqid
    #
    @2
    eqid
    #
    zrhmulg
    mpdan
    @0
    @4
    @2
    cR
    cod
    cfv
    #
    cfv
    #
    @2
    @3
    co
    #
    c.0
    @8
    cC
    @2
    @3
    cC
    cR
    @2
    @7
    @7
    eqid
    #
    @6
    chrcl.c
    chrval
    oveq1i
    @0
    @2
    cR
    cbs
    cfv
    #
    wcel
    @9
    c.0
    wceq
    @11
    cR
    @2
    @11
    eqid
    #
    @6
    ringidcl
    @2
    @3
    cR
    @7
    @11
    c.0
    @12
    @10
    @5
    chrid.z
    odid
    syl
    syl5eqr
    eqtrd
end

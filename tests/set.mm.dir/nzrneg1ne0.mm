include "cnzr.mm"
include "wcel.mm"
include "cur.mm"
include "cfv.mm"
include "cminusg.mm"
include "cui.mm"
include "c0g.mm"
include "wne.mm"
include "crg.mm"
include "nzrring.mm"
include "eqid.mm"
include "1unit.mm"
include "syl.mm"
include "unitnegcl.mm"
include "syl2anc.mm"
include "nzrunit.mm"
include "mpdan.mm"

theorem nzrneg1ne0
  let cR: class R
  let vk: setvar k
  let vx: setvar x


  assert |- ( R e. NzRing -> ( ( invg ` R ) ` ( 1r ` R ) ) =/= ( 0g ` R ) )

  proof
    cR
    cnzr
    wcel
    #
    cR
    cur
    cfv
    #
    cR
    cminusg
    cfv
    #
    cfv
    #
    cR
    cui
    cfv
    #
    wcel
    #
    @3
    cR
    c0g
    cfv
    #
    wne
    @0
    cR
    crg
    wcel
    #
    @1
    @4
    wcel
    #
    @5
    cR
    nzrring
    #
    @0
    @7
    @8
    @9
    cR
    @4
    @1
    @4
    eqid
    #
    @1
    eqid
    1unit
    syl
    cR
    @4
    @2
    @1
    @10
    @2
    eqid
    unitnegcl
    syl2anc
    @3
    cR
    @4
    @6
    @10
    @6
    eqid
    nzrunit
    mpdan
end

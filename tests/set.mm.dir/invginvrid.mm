include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cur.mm"
include "cmgp.mm"
include "cmnd.mm"
include "wceq.mm"
include "eqid.mm"
include "ringmgp.mm"
include "3ad2ant1.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "unitcl.mm"
include "grpinvcl.mm"
include "syl2an.mm"
include "3adant2.mm"
include "unitnegcl.mm"
include "ringinvcl.mm"
include "syldan.mm"
include "simp2.mm"
include "wa.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "mndass.mm"
include "eqcomd.mm"
include "syl13anc.mm"
include "simp1.mm"
include "unitrinv.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "ringlidm.mm"
include "3adant3.mm"
include "3eqtrd.mm"

theorem invginvrid
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let cI: class I
  let cN: class N
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume invginvrid.b: |- B = ( Base ` R )
  assume invginvrid.u: |- U = ( Unit ` R )
  assume invginvrid.n: |- N = ( invg ` R )
  assume invginvrid.i: |- I = ( invr ` R )
  assume invginvrid.t: |- .x. = ( .r ` R )


  assert |- ( ( R e. Ring /\ X e. B /\ Y e. U ) -> ( ( N ` Y ) .x. ( ( I ` ( N ` Y ) ) .x. X ) ) = X )

  proof
    cR
    crg
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cU
    wcel
    #
    w3a
    #
    cY
    cN
    cfv
    #
    @4
    cI
    cfv
    #
    cX
    c.x
    co
    c.x
    co
    #
    @4
    @5
    c.x
    co
    #
    cX
    c.x
    co
    #
    cR
    cur
    cfv
    #
    cX
    c.x
    co
    #
    cX
    @3
    cR
    cmgp
    cfv
    #
    cmnd
    wcel
    #
    @4
    cB
    wcel
    #
    @5
    cB
    wcel
    #
    @1
    @6
    @8
    wceq
    @0
    @1
    @12
    @2
    cR
    @11
    @11
    eqid
    #
    ringmgp
    3ad2ant1
    @0
    @2
    @13
    @1
    @0
    cR
    cgrp
    wcel
    cY
    cB
    wcel
    @13
    @2
    cR
    ringgrp
    cB
    cR
    cU
    cY
    invginvrid.b
    invginvrid.u
    unitcl
    cB
    cR
    cN
    cY
    invginvrid.b
    invginvrid.n
    grpinvcl
    syl2an
    3adant2
    @0
    @2
    @14
    @1
    @0
    @2
    @4
    cU
    wcel
    #
    @14
    cR
    cU
    cN
    cY
    invginvrid.u
    invginvrid.n
    unitnegcl
    #
    cB
    cR
    cU
    cI
    @4
    invginvrid.u
    invginvrid.i
    invginvrid.b
    ringinvcl
    syldan
    3adant2
    @0
    @1
    @2
    simp2
    @12
    @13
    @14
    @1
    w3a
    wa
    @8
    @6
    cB
    c.x
    @11
    @4
    @5
    cX
    cB
    cR
    @11
    @15
    invginvrid.b
    mgpbas
    cR
    c.x
    @11
    @15
    invginvrid.t
    mgpplusg
    mndass
    eqcomd
    syl13anc
    @3
    @7
    @9
    cX
    c.x
    @3
    @0
    @16
    @7
    @9
    wceq
    @0
    @1
    @2
    simp1
    @0
    @2
    @16
    @1
    @17
    3adant2
    cR
    c.x
    cU
    @9
    cI
    @4
    invginvrid.u
    invginvrid.i
    invginvrid.t
    @9
    eqid
    #
    unitrinv
    syl2anc
    oveq1d
    @0
    @1
    @10
    cX
    wceq
    @2
    cB
    cR
    c.x
    @9
    cX
    invginvrid.b
    invginvrid.t
    @18
    ringlidm
    3adant3
    3eqtrd
end

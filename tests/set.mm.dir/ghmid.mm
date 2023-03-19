include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "cplusg.mm"
include "wceq.mm"
include "cbs.mm"
include "cgrp.mm"
include "ghmgrp1.mm"
include "eqid.mm"
include "grpidcl.mm"
include "syl.mm"
include "ghmlin.mm"
include "mpd3an23.mm"
include "grplid.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "wb.mm"
include "ghmgrp2.mm"
include "ghmf.mm"
include "ffvelrnd.mm"
include "grpid.mm"
include "mpbid.mm"
include "eqcomd.mm"

theorem ghmid
  let cS: class S
  let cT: class T
  let cF: class F
  let cY: class Y
  let c.0: class .0.
  assume ghmid.y: |- Y = ( 0g ` S )
  assume ghmid.z: |- .0. = ( 0g ` T )


  assert |- ( F e. ( S GrpHom T ) -> ( F ` Y ) = .0. )

  proof
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    c.0
    cY
    cF
    cfv
    #
    @0
    @1
    @1
    cT
    cplusg
    cfv
    #
    co
    #
    @1
    wceq
    #
    c.0
    @1
    wceq
    #
    @0
    cY
    cY
    cS
    cplusg
    cfv
    #
    co
    #
    cF
    cfv
    #
    @3
    @1
    @0
    cY
    cS
    cbs
    cfv
    #
    wcel
    #
    @10
    @8
    @3
    wceq
    @0
    cS
    cgrp
    wcel
    #
    @10
    cS
    cT
    cF
    ghmgrp1
    #
    @9
    cS
    cY
    @9
    eqid
    #
    ghmid.y
    grpidcl
    syl
    #
    @14
    @6
    @2
    cS
    cT
    cY
    cF
    cY
    @9
    @13
    @6
    eqid
    #
    @2
    eqid
    #
    ghmlin
    mpd3an23
    @0
    @7
    cY
    cF
    @0
    @11
    @10
    @7
    cY
    wceq
    @12
    @14
    @9
    @6
    cS
    cY
    cY
    @13
    @15
    ghmid.y
    grplid
    syl2anc
    fveq2d
    eqtr3d
    @0
    cT
    cgrp
    wcel
    @1
    cT
    cbs
    cfv
    #
    wcel
    @4
    @5
    wb
    cS
    cT
    cF
    ghmgrp2
    @0
    @9
    @17
    cY
    cF
    cS
    cT
    cF
    @9
    @17
    @13
    @17
    eqid
    #
    ghmf
    @14
    ffvelrnd
    @17
    @2
    cT
    @1
    c.0
    @18
    @16
    ghmid.z
    grpid
    syl2anc
    mpbid
    eqcomd
end

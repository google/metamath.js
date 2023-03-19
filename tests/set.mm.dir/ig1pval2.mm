include "crg.mm"
include "wcel.mm"
include "csn.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cdg1.mm"
include "cdif.mm"
include "cima.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cmn1.mm"
include "cin.mm"
include "crio.mm"
include "cif.mm"
include "clidl.mm"
include "ply1ring.mm"
include "eqid.mm"
include "lidl0.mm"
include "syl.mm"
include "ig1pval.mm"
include "mpdan.mm"
include "iftruei.mm"
include "syl6eq.mm"

theorem ig1pval2
  let cP: class P
  let cR: class R
  let cG: class G
  let c.0: class .0.
  let vg: setvar g
  assume ig1pval.p: |- P = ( Poly1 ` R )
  assume ig1pval.g: |- G = ( idlGen1p ` R )
  assume ig1pval2.z: |- .0. = ( 0g ` P )


  assert |- ( R e. Ring -> ( G ` { .0. } ) = .0. )

  proof
    cR
    crg
    wcel
    #
    c.0
    csn
    #
    cG
    cfv
    #
    @1
    @1
    wceq
    #
    c.0
    vg
    cv
    cR
    cdg1
    cfv
    #
    cfv
    @4
    @1
    @1
    cdif
    cima
    cr
    clt
    cinf
    wceq
    vg
    @1
    cR
    cmn1
    cfv
    #
    cin
    crio
    #
    cif
    #
    c.0
    @0
    @1
    cP
    clidl
    cfv
    #
    wcel
    #
    @2
    @7
    wceq
    @0
    cP
    crg
    wcel
    @9
    cP
    cR
    ig1pval.p
    ply1ring
    cP
    @8
    c.0
    @8
    eqid
    #
    ig1pval2.z
    lidl0
    syl
    @4
    cP
    cR
    @8
    vg
    cG
    @1
    @5
    crg
    c.0
    ig1pval.p
    ig1pval.g
    ig1pval2.z
    @10
    @4
    eqid
    @5
    eqid
    ig1pval
    mpdan
    @3
    c.0
    @6
    @1
    eqid
    iftruei
    syl6eq
end

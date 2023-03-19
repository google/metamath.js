include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "weq.mm"
include "cif.mm"
include "wral.mm"
include "cv.mm"
include "wa.mm"
include "crg.mm"
include "ringidcl.mm"
include "ring0cl.mm"
include "ifcld.mm"
include "syl.mm"
include "adantr.mm"
include "ralrimivva.mm"
include "fmpt2.mm"
include "sylib.mm"
include "cvv.mm"
include "cfn.mm"
include "wb.mm"
include "cbs.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpfi.mm"
include "syl2anc.mm"
include "elmapg.mm"
include "sylancr.mm"
include "mpbird.mm"

theorem mamumat1cl
  let wph: wff ph
  let cB: class B
  let cR: class R
  let c.1: class .1.
  let vi: setvar i
  let vj: setvar j
  let cI: class I
  let cM: class M
  let c.0: class .0.
  assume mamumat1cl.b: |- B = ( Base ` R )
  assume mamumat1cl.r: |- ( ph -> R e. Ring )
  assume mamumat1cl.o: |- .1. = ( 1r ` R )
  assume mamumat1cl.z: |- .0. = ( 0g ` R )
  assume mamumat1cl.i: |- I = ( i e. M , j e. M |-> if ( i = j , .1. , .0. ) )
  assume mamumat1cl.m: |- ( ph -> M e. Fin )

  disjoint i j
  disjoint B i
  disjoint B j
  disjoint M i
  disjoint M j
  disjoint i ph
  disjoint j ph
  assert |- ( ph -> I e. ( B ^m ( M X. M ) ) )

  proof
    wph
    cI
    cB
    cM
    cM
    cxp
    #
    cmap
    co
    wcel
    #
    @0
    cB
    cI
    wf
    #
    wph
    vi
    vj
    weq
    #
    c.1
    c.0
    cif
    #
    cB
    wcel
    #
    vj
    cM
    wral
    vi
    cM
    wral
    @2
    wph
    @5
    vi
    vj
    cM
    cM
    wph
    @5
    vi
    cv
    cM
    wcel
    vj
    cv
    cM
    wcel
    wa
    wph
    cR
    crg
    wcel
    #
    @5
    mamumat1cl.r
    @6
    @3
    c.1
    c.0
    cB
    cB
    cR
    c.1
    mamumat1cl.b
    mamumat1cl.o
    ringidcl
    cB
    cR
    c.0
    mamumat1cl.b
    mamumat1cl.z
    ring0cl
    ifcld
    syl
    adantr
    ralrimivva
    vi
    vj
    cM
    cM
    @4
    cB
    cI
    mamumat1cl.i
    fmpt2
    sylib
    wph
    cB
    cvv
    wcel
    @0
    cfn
    wcel
    #
    @1
    @2
    wb
    cB
    cR
    cbs
    cfv
    cvv
    mamumat1cl.b
    cR
    cbs
    fvex
    eqeltri
    wph
    cM
    cfn
    wcel
    #
    @8
    @7
    mamumat1cl.m
    mamumat1cl.m
    cM
    cM
    xpfi
    syl2anc
    cB
    @0
    cI
    cvv
    cfn
    elmapg
    sylancr
    mpbird
end

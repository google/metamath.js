include "co.mm"
include "cfv.mm"
include "cof.mm"
include "clmod.mm"
include "ldualvadd.mm"
include "fveq1d.mm"
include "wcel.mm"
include "wceq.mm"
include "cvv.mm"
include "wfn.mm"
include "wa.mm"
include "cbs.mm"
include "wf.mm"
include "eqid.mm"
include "lflf.mm"
include "ffn.mm"
include "syl.mm"
include "syl2anc.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "inidm.mm"
include "eqidd.mm"
include "ofval.mm"
include "mpdan.mm"
include "eqtrd.mm"

theorem ldualvaddval
  let wph: wff ph
  let cD: class D
  let c.pl: class .+
  let c.pb: class .+b
  let cR: class R
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let cW: class W
  let cX: class X
  assume ldualvaddval.v: |- V = ( Base ` W )
  assume ldualvaddval.r: |- R = ( Scalar ` W )
  assume ldualvaddval.a: |- .+ = ( +g ` R )
  assume ldualvaddval.f: |- F = ( LFnl ` W )
  assume ldualvaddval.d: |- D = ( LDual ` W )
  assume ldualvaddval.p: |- .+b = ( +g ` D )
  assume ldualvaddval.w: |- ( ph -> W e. LMod )
  assume ldualvaddval.g: |- ( ph -> G e. F )
  assume ldualvaddval.h: |- ( ph -> H e. F )
  assume ldualvaddval.x: |- ( ph -> X e. V )


  assert |- ( ph -> ( ( G .+b H ) ` X ) = ( ( G ` X ) .+ ( H ` X ) ) )

  proof
    wph
    cX
    cG
    cH
    c.pb
    co
    #
    cfv
    cX
    cG
    cH
    c.pl
    cof
    co
    #
    cfv
    #
    cX
    cG
    cfv
    #
    cX
    cH
    cfv
    #
    c.pl
    co
    #
    wph
    cX
    @0
    @1
    wph
    cD
    c.pl
    c.pb
    cR
    cF
    cG
    cH
    cW
    clmod
    ldualvaddval.f
    ldualvaddval.r
    ldualvaddval.a
    ldualvaddval.d
    ldualvaddval.p
    ldualvaddval.w
    ldualvaddval.g
    ldualvaddval.h
    ldualvadd
    fveq1d
    wph
    cX
    cV
    wcel
    #
    @2
    @5
    wceq
    ldualvaddval.x
    wph
    cV
    cV
    @3
    @4
    c.pl
    cV
    cG
    cH
    cvv
    cvv
    cX
    wph
    cW
    clmod
    wcel
    #
    cG
    cF
    wcel
    #
    cG
    cV
    wfn
    #
    ldualvaddval.w
    ldualvaddval.g
    @7
    @8
    wa
    cV
    cR
    cbs
    cfv
    #
    cG
    wf
    @9
    cR
    cF
    cG
    @10
    cV
    cW
    clmod
    ldualvaddval.r
    @10
    eqid
    #
    ldualvaddval.v
    ldualvaddval.f
    lflf
    cV
    @10
    cG
    ffn
    syl
    syl2anc
    wph
    @7
    cH
    cF
    wcel
    #
    cH
    cV
    wfn
    #
    ldualvaddval.w
    ldualvaddval.h
    @7
    @12
    wa
    cV
    @10
    cH
    wf
    @13
    cR
    cF
    cH
    @10
    cV
    cW
    clmod
    ldualvaddval.r
    @11
    ldualvaddval.v
    ldualvaddval.f
    lflf
    cV
    @10
    cH
    ffn
    syl
    syl2anc
    cV
    cvv
    wcel
    wph
    cV
    cW
    cbs
    cfv
    cvv
    ldualvaddval.v
    cW
    cbs
    fvex
    eqeltri
    a1i
    #
    @14
    cV
    inidm
    wph
    @6
    wa
    #
    @3
    eqidd
    @15
    @4
    eqidd
    ofval
    mpdan
    eqtrd
end

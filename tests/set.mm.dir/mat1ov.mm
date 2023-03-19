include "weq.mm"
include "cif.mm"
include "wceq.mm"
include "cvv.mm"
include "cur.mm"
include "cfv.mm"
include "cmpt2.mm"
include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "mat1.mm"
include "syl2anc.mm"
include "syl5eq.mm"
include "cv.mm"
include "wa.mm"
include "eqeq12.mm"
include "ifbid.mm"
include "adantl.mm"
include "fvex.mm"
include "eqeltri.mm"
include "c0g.mm"
include "ifex.mm"
include "a1i.mm"
include "ovmpt2d.mm"

theorem mat1ov
  let wph: wff ph
  let cA: class A
  let cR: class R
  let cU: class U
  let c.1: class .1.
  let cI: class I
  let cJ: class J
  let cN: class N
  let c.0: class .0.
  let vi: setvar i
  let vj: setvar j
  let vx: setvar x
  assume mat1.a: |- A = ( N Mat R )
  assume mat1.o: |- .1. = ( 1r ` R )
  assume mat1.z: |- .0. = ( 0g ` R )
  assume mat1ov.n: |- ( ph -> N e. Fin )
  assume mat1ov.r: |- ( ph -> R e. Ring )
  assume mat1ov.i: |- ( ph -> I e. N )
  assume mat1ov.j: |- ( ph -> J e. N )
  assume mat1ov.u: |- U = ( 1r ` A )


  assert |- ( ph -> ( I U J ) = if ( I = J , .1. , .0. ) )

  proof
    wph
    vi
    vj
    cI
    cJ
    cN
    cN
    vi
    vj
    weq
    #
    c.1
    c.0
    cif
    #
    cI
    cJ
    wceq
    #
    c.1
    c.0
    cif
    #
    cU
    cvv
    wph
    cU
    cA
    cur
    cfv
    #
    vi
    vj
    cN
    cN
    @1
    cmpt2
    #
    mat1ov.u
    wph
    cN
    cfn
    wcel
    cR
    crg
    wcel
    @4
    @5
    wceq
    mat1ov.n
    mat1ov.r
    cA
    cR
    c.1
    vi
    vj
    cN
    c.0
    mat1.a
    mat1.o
    mat1.z
    mat1
    syl2anc
    syl5eq
    vi
    cv
    #
    cI
    wceq
    vj
    cv
    #
    cJ
    wceq
    wa
    #
    @1
    @3
    wceq
    wph
    @8
    @0
    @2
    c.1
    c.0
    @6
    cI
    @7
    cJ
    eqeq12
    ifbid
    adantl
    mat1ov.i
    mat1ov.j
    @3
    cvv
    wcel
    wph
    @2
    c.1
    c.0
    c.1
    cR
    cur
    cfv
    cvv
    mat1.o
    cR
    cur
    fvex
    eqeltri
    c.0
    cR
    c0g
    cfv
    cvv
    mat1.z
    cR
    c0g
    fvex
    eqeltri
    ifex
    a1i
    ovmpt2d
end

include "cld.mm"
include "cfv.mm"
include "cvsca.mm"
include "clfn.mm"
include "eqid.mm"
include "dvhlvec.mm"
include "lcdvbaselfl.mm"
include "co.mm"
include "lcdvs.mm"
include "oveqd.mm"
include "eqtrd.mm"
include "lkreqN.mm"

theorem lcdlkreq2N
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cL: class L
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume lcdlkreq2.h: |- H = ( LHyp ` K )
  assume lcdlkreq2.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcdlkreq2.s: |- S = ( Scalar ` U )
  assume lcdlkreq2.r: |- R = ( Base ` S )
  assume lcdlkreq2.o: |- .0. = ( 0g ` S )
  assume lcdlkreq2.l: |- L = ( LKer ` U )
  assume lcdlkreq2.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdlkreq2.v: |- V = ( Base ` C )
  assume lcdlkreq2.t: |- .x. = ( .s ` C )
  assume lcdlkreq2.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcdlkreq2.a: |- ( ph -> A e. ( R \ { .0. } ) )
  assume lcdlkreq2.i: |- ( ph -> I e. V )
  assume lcdlkreq2.g: |- ( ph -> G = ( A .x. I ) )


  assert |- ( ph -> ( L ` G ) = ( L ` I ) )

  proof
    wph
    cA
    cU
    cld
    cfv
    #
    cR
    cS
    @0
    cvsca
    cfv
    #
    cU
    clfn
    cfv
    #
    cG
    cI
    cL
    cU
    c.0
    lcdlkreq2.s
    lcdlkreq2.r
    lcdlkreq2.o
    @2
    eqid
    #
    lcdlkreq2.l
    @0
    eqid
    #
    @1
    eqid
    #
    wph
    cU
    cH
    cK
    cW
    lcdlkreq2.h
    lcdlkreq2.u
    lcdlkreq2.k
    dvhlvec
    lcdlkreq2.a
    wph
    cC
    cU
    @2
    cH
    cK
    cV
    cW
    cI
    lcdlkreq2.h
    lcdlkreq2.c
    lcdlkreq2.v
    lcdlkreq2.u
    @3
    lcdlkreq2.k
    lcdlkreq2.i
    lcdvbaselfl
    wph
    cG
    cA
    cI
    c.x
    co
    cA
    cI
    @1
    co
    lcdlkreq2.g
    wph
    c.x
    @1
    cA
    cI
    wph
    cC
    @0
    c.x
    @1
    cU
    cH
    cK
    cW
    lcdlkreq2.h
    lcdlkreq2.u
    @4
    @5
    lcdlkreq2.c
    lcdlkreq2.t
    lcdlkreq2.k
    lcdvs
    oveqd
    eqtrd
    lkreqN
end

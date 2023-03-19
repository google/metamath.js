include "cfv.mm"
include "cin.mm"
include "cur.mm"
include "cminusg.mm"
include "co.mm"
include "cplusg.mm"
include "wss.mm"
include "cbs.mm"
include "eqid.mm"
include "crg.mm"
include "wcel.mm"
include "clmod.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "lmodring.mm"
include "cdr.mm"
include "wne.mm"
include "lvecdrng.mm"
include "lflcl.mm"
include "syl3anc.mm"
include "drnginvrcl.mm"
include "ringcl.mm"
include "lkrss.mm"
include "ldualvscl.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "ringidcl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "sstrd.mm"
include "sslin.mm"
include "lkrin.mm"
include "fveq2i.mm"
include "ldualvsub.mm"
include "fveq2d.mm"
include "syl5req.mm"
include "sseqtrd.mm"

theorem lcfrlem2
  let wph: wff ph
  let cD: class D
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let cV: class V
  let cX: class X
  let c.0: class .0.
  assume lcfrlem1.v: |- V = ( Base ` U )
  assume lcfrlem1.s: |- S = ( Scalar ` U )
  assume lcfrlem1.q: |- .X. = ( .r ` S )
  assume lcfrlem1.z: |- .0. = ( 0g ` S )
  assume lcfrlem1.i: |- I = ( invr ` S )
  assume lcfrlem1.f: |- F = ( LFnl ` U )
  assume lcfrlem1.d: |- D = ( LDual ` U )
  assume lcfrlem1.t: |- .x. = ( .s ` D )
  assume lcfrlem1.m: |- .- = ( -g ` D )
  assume lcfrlem1.u: |- ( ph -> U e. LVec )
  assume lcfrlem1.e: |- ( ph -> E e. F )
  assume lcfrlem1.g: |- ( ph -> G e. F )
  assume lcfrlem1.x: |- ( ph -> X e. V )
  assume lcfrlem1.n: |- ( ph -> ( G ` X ) =/= .0. )
  assume lcfrlem1.h: |- H = ( E .- ( ( ( I ` ( G ` X ) ) .X. ( E ` X ) ) .x. G ) )
  assume lcfrlem2.l: |- L = ( LKer ` U )


  assert |- ( ph -> ( ( L ` E ) i^i ( L ` G ) ) C_ ( L ` H ) )

  proof
    wph
    cE
    cL
    cfv
    #
    cG
    cL
    cfv
    #
    cin
    #
    cE
    cS
    cur
    cfv
    #
    cS
    cminusg
    cfv
    #
    cfv
    #
    cX
    cG
    cfv
    #
    cI
    cfv
    #
    cX
    cE
    cfv
    #
    c.xp
    co
    #
    cG
    c.x
    co
    #
    c.x
    co
    #
    cD
    cplusg
    cfv
    #
    co
    #
    cL
    cfv
    #
    cH
    cL
    cfv
    #
    wph
    @2
    @0
    @11
    cL
    cfv
    #
    cin
    #
    @14
    wph
    @1
    @16
    wss
    @2
    @17
    wss
    wph
    @1
    @10
    cL
    cfv
    @16
    wph
    cD
    cS
    c.x
    cF
    cG
    cS
    cbs
    cfv
    #
    cL
    cU
    @9
    lcfrlem1.s
    @18
    eqid
    #
    lcfrlem1.f
    lcfrlem2.l
    lcfrlem1.d
    lcfrlem1.t
    lcfrlem1.u
    lcfrlem1.g
    wph
    cS
    crg
    wcel
    #
    @7
    @18
    wcel
    #
    @8
    @18
    wcel
    #
    @9
    @18
    wcel
    wph
    cU
    clmod
    wcel
    #
    @20
    wph
    cU
    clvec
    wcel
    #
    @23
    lcfrlem1.u
    cU
    lveclmod
    syl
    #
    cS
    cU
    lcfrlem1.s
    lmodring
    syl
    #
    wph
    cS
    cdr
    wcel
    #
    @6
    @18
    wcel
    #
    @6
    c.0
    wne
    @21
    wph
    @24
    @27
    lcfrlem1.u
    cS
    cU
    lcfrlem1.s
    lvecdrng
    syl
    wph
    @24
    cG
    cF
    wcel
    cX
    cV
    wcel
    #
    @28
    lcfrlem1.u
    lcfrlem1.g
    lcfrlem1.x
    cS
    cF
    cG
    @18
    cV
    cU
    cX
    clvec
    lcfrlem1.s
    @19
    lcfrlem1.v
    lcfrlem1.f
    lflcl
    syl3anc
    lcfrlem1.n
    @18
    cS
    cI
    @6
    c.0
    @19
    lcfrlem1.z
    lcfrlem1.i
    drnginvrcl
    syl3anc
    wph
    @24
    cE
    cF
    wcel
    @29
    @22
    lcfrlem1.u
    lcfrlem1.e
    lcfrlem1.x
    cS
    cF
    cE
    @18
    cV
    cU
    cX
    clvec
    lcfrlem1.s
    @19
    lcfrlem1.v
    lcfrlem1.f
    lflcl
    syl3anc
    @18
    cS
    c.xp
    @7
    @8
    @19
    lcfrlem1.q
    ringcl
    syl3anc
    #
    lkrss
    wph
    cD
    cS
    c.x
    cF
    @10
    @18
    cL
    cU
    @5
    lcfrlem1.s
    @19
    lcfrlem1.f
    lcfrlem2.l
    lcfrlem1.d
    lcfrlem1.t
    lcfrlem1.u
    wph
    cD
    cS
    c.x
    cF
    cG
    @18
    cU
    @9
    lcfrlem1.f
    lcfrlem1.s
    @19
    lcfrlem1.d
    lcfrlem1.t
    @25
    @30
    lcfrlem1.g
    ldualvscl
    #
    wph
    cS
    cgrp
    wcel
    #
    @3
    @18
    wcel
    #
    @5
    @18
    wcel
    wph
    @20
    @32
    @26
    cS
    ringgrp
    syl
    wph
    @20
    @33
    @26
    @18
    cS
    @3
    @19
    @3
    eqid
    #
    ringidcl
    syl
    @18
    cS
    @4
    @3
    @19
    @4
    eqid
    #
    grpinvcl
    syl2anc
    #
    lkrss
    sstrd
    @1
    @16
    @0
    sslin
    syl
    wph
    cD
    @12
    cF
    cE
    @11
    cL
    cU
    lcfrlem1.f
    lcfrlem2.l
    lcfrlem1.d
    @12
    eqid
    #
    @25
    lcfrlem1.e
    wph
    cD
    cS
    c.x
    cF
    @10
    @18
    cU
    @5
    lcfrlem1.f
    lcfrlem1.s
    @19
    lcfrlem1.d
    lcfrlem1.t
    @25
    @36
    @31
    ldualvscl
    lkrin
    sstrd
    wph
    @15
    cE
    @10
    c.mi
    co
    #
    cL
    cfv
    @14
    cH
    @38
    cL
    lcfrlem1.h
    fveq2i
    wph
    @38
    @13
    cL
    wph
    cD
    @12
    cS
    c.x
    @3
    cF
    cE
    @10
    c.mi
    @4
    cU
    lcfrlem1.s
    @35
    @34
    lcfrlem1.f
    lcfrlem1.d
    @37
    lcfrlem1.t
    lcfrlem1.m
    @25
    lcfrlem1.e
    @31
    ldualvsub
    fveq2d
    syl5req
    sseqtrd
end

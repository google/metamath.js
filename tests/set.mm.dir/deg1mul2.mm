include "co.mm"
include "cfv.mm"
include "caddc.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "crg.mm"
include "wcel.mm"
include "wne.mm"
include "cn0.mm"
include "deg1nn0cl.mm"
include "syl3anc.mm"
include "nn0red.mm"
include "leidd.mm"
include "deg1mulle2.mm"
include "cco1.mm"
include "c0g.mm"
include "ply1ring.mm"
include "syl.mm"
include "ringcl.mm"
include "nn0addcld.mm"
include "cmulr.mm"
include "eqid.mm"
include "coe1mul4.mm"
include "deg1ldg.mm"
include "cbs.mm"
include "wi.mm"
include "wf.mm"
include "coe1f.mm"
include "ffvelrnd.mm"
include "rrgeq0i.mm"
include "syl2anc.mm"
include "necon3d.mm"
include "mpd.mm"
include "eqnetrd.mm"
include "deg1ge.mm"
include "cxr.mm"
include "wa.mm"
include "wb.mm"
include "deg1xrcl.mm"
include "rexrd.mm"
include "xrletri3.mm"
include "mpbir2and.mm"

theorem deg1mul2
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let cE: class E
  let cF: class F
  let cG: class G
  let c.0: class .0.
  assume deg1mul2.d: |- D = ( deg1 ` R )
  assume deg1mul2.p: |- P = ( Poly1 ` R )
  assume deg1mul2.e: |- E = ( RLReg ` R )
  assume deg1mul2.b: |- B = ( Base ` P )
  assume deg1mul2.t: |- .x. = ( .r ` P )
  assume deg1mul2.z: |- .0. = ( 0g ` P )
  assume deg1mul2.r: |- ( ph -> R e. Ring )
  assume deg1mul2.fb: |- ( ph -> F e. B )
  assume deg1mul2.fz: |- ( ph -> F =/= .0. )
  assume deg1mul2.fc: |- ( ph -> ( ( coe1 ` F ) ` ( D ` F ) ) e. E )
  assume deg1mul2.gb: |- ( ph -> G e. B )
  assume deg1mul2.gz: |- ( ph -> G =/= .0. )


  assert |- ( ph -> ( D ` ( F .x. G ) ) = ( ( D ` F ) + ( D ` G ) ) )

  proof
    wph
    cF
    cG
    c.x
    co
    #
    cD
    cfv
    #
    cF
    cD
    cfv
    #
    cG
    cD
    cfv
    #
    caddc
    co
    #
    wceq
    #
    @1
    @4
    cle
    wbr
    #
    @4
    @1
    cle
    wbr
    #
    wph
    cB
    cD
    cR
    c.x
    cF
    cG
    @2
    @3
    cP
    deg1mul2.p
    deg1mul2.d
    deg1mul2.r
    deg1mul2.b
    deg1mul2.t
    deg1mul2.fb
    deg1mul2.gb
    wph
    cR
    crg
    wcel
    #
    cF
    cB
    wcel
    #
    cF
    c.0
    wne
    @2
    cn0
    wcel
    deg1mul2.r
    deg1mul2.fb
    deg1mul2.fz
    cB
    cD
    cP
    cR
    cF
    c.0
    deg1mul2.d
    deg1mul2.p
    deg1mul2.z
    deg1mul2.b
    deg1nn0cl
    syl3anc
    #
    wph
    @8
    cG
    cB
    wcel
    #
    cG
    c.0
    wne
    #
    @3
    cn0
    wcel
    deg1mul2.r
    deg1mul2.gb
    deg1mul2.gz
    cB
    cD
    cP
    cR
    cG
    c.0
    deg1mul2.d
    deg1mul2.p
    deg1mul2.z
    deg1mul2.b
    deg1nn0cl
    syl3anc
    #
    wph
    @2
    wph
    @2
    @10
    nn0red
    leidd
    wph
    @3
    wph
    @3
    @13
    nn0red
    leidd
    deg1mulle2
    wph
    @0
    cB
    wcel
    #
    @4
    cn0
    wcel
    @4
    @0
    cco1
    cfv
    #
    cfv
    #
    cR
    c0g
    cfv
    #
    wne
    @7
    wph
    cP
    crg
    wcel
    #
    @9
    @11
    @14
    wph
    @8
    @18
    deg1mul2.r
    cP
    cR
    deg1mul2.p
    ply1ring
    syl
    deg1mul2.fb
    deg1mul2.gb
    cB
    cP
    c.x
    cF
    cG
    deg1mul2.b
    deg1mul2.t
    ringcl
    syl3anc
    #
    wph
    @2
    @3
    @10
    @13
    nn0addcld
    #
    wph
    @16
    @2
    cF
    cco1
    cfv
    cfv
    #
    @3
    cG
    cco1
    cfv
    #
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    @17
    wph
    cB
    cD
    cR
    c.x
    @24
    cF
    cG
    cP
    c.0
    deg1mul2.p
    deg1mul2.t
    @24
    eqid
    #
    deg1mul2.b
    deg1mul2.d
    deg1mul2.z
    deg1mul2.r
    deg1mul2.fb
    deg1mul2.fz
    deg1mul2.gb
    deg1mul2.gz
    coe1mul4
    wph
    @23
    @17
    wne
    #
    @25
    @17
    wne
    wph
    @8
    @11
    @12
    @27
    deg1mul2.r
    deg1mul2.gb
    deg1mul2.gz
    @22
    cB
    cD
    cP
    cR
    cG
    @17
    c.0
    deg1mul2.d
    deg1mul2.p
    deg1mul2.z
    deg1mul2.b
    @17
    eqid
    #
    @22
    eqid
    #
    deg1ldg
    syl3anc
    wph
    @25
    @17
    @23
    @17
    wph
    @21
    cE
    wcel
    @23
    cR
    cbs
    cfv
    #
    wcel
    @25
    @17
    wceq
    @23
    @17
    wceq
    wi
    deg1mul2.fc
    wph
    cn0
    @30
    @3
    @22
    wph
    @11
    cn0
    @30
    @22
    wf
    deg1mul2.gb
    @22
    cB
    cP
    cR
    cG
    @30
    @29
    deg1mul2.b
    deg1mul2.p
    @30
    eqid
    #
    coe1f
    syl
    @13
    ffvelrnd
    @30
    cR
    @24
    cE
    @21
    @23
    @17
    deg1mul2.e
    @31
    @26
    @28
    rrgeq0i
    syl2anc
    necon3d
    mpd
    eqnetrd
    @15
    cB
    cD
    cP
    cR
    @0
    @4
    @17
    deg1mul2.d
    deg1mul2.p
    deg1mul2.b
    @28
    @15
    eqid
    deg1ge
    syl3anc
    wph
    @1
    cxr
    wcel
    #
    @4
    cxr
    wcel
    @5
    @6
    @7
    wa
    wb
    wph
    @14
    @32
    @19
    cB
    cD
    cP
    cR
    @0
    deg1mul2.d
    deg1mul2.p
    deg1mul2.b
    deg1xrcl
    syl
    wph
    @4
    wph
    @4
    @20
    nn0red
    rexrd
    @1
    @4
    xrletri3
    syl2anc
    mpbir2and
end

include "clm.mm"
include "cfv.mm"
include "wbr.mm"
include "crest.mm"
include "co.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cli.mm"
include "c1.mm"
include "cvv.mm"
include "cn.mm"
include "eqid.mm"
include "nnuz.mm"
include "cc.mm"
include "wcel.mm"
include "cnex.mm"
include "a1i.mm"
include "wss.mm"
include "ssexd.mm"
include "ctop.mm"
include "topontopi.mm"
include "cz.mm"
include "1z.mm"
include "lmss.mm"
include "wb.mm"
include "fveq2i.mm"
include "breqi.mm"
include "cnfldtop.mm"
include "wf.mm"
include "fss.mm"
include "sylancl.mm"
include "lmclimf.mm"
include "sylancr.mm"
include "bitr3d.mm"
include "3bitrd.mm"

theorem lmlim
  let wph: wff ph
  let cP: class P
  let cF: class F
  let cJ: class J
  let cX: class X
  let cY: class Y
  assume lmlim.j: |- J e. ( TopOn ` Y )
  assume lmlim.f: |- ( ph -> F : NN --> X )
  assume lmlim.p: |- ( ph -> P e. X )
  assume lmlim.t: |- ( J |`t X ) = ( ( TopOpen ` CCfld ) |`t X )
  assume lmlim.x: |- X C_ CC


  assert |- ( ph -> ( F ( ~~>t ` J ) P <-> F ~~> P ) )

  proof
    wph
    cF
    cP
    cJ
    clm
    cfv
    wbr
    cF
    cP
    cJ
    cX
    crest
    co
    #
    clm
    cfv
    #
    wbr
    #
    cF
    cP
    ccnfld
    ctopn
    cfv
    #
    cX
    crest
    co
    #
    clm
    cfv
    #
    wbr
    #
    cF
    cP
    cli
    wbr
    #
    wph
    cP
    cF
    cJ
    @0
    c1
    cvv
    cX
    cn
    @0
    eqid
    nnuz
    wph
    cX
    cc
    cvv
    cc
    cvv
    wcel
    wph
    cnex
    a1i
    cX
    cc
    wss
    #
    wph
    lmlim.x
    a1i
    ssexd
    #
    cJ
    ctop
    wcel
    wph
    cY
    cJ
    lmlim.j
    topontopi
    a1i
    lmlim.p
    c1
    cz
    wcel
    #
    wph
    1z
    a1i
    #
    lmlim.f
    lmss
    @2
    @6
    wb
    wph
    cF
    cP
    @1
    @5
    @0
    @4
    clm
    lmlim.t
    fveq2i
    breqi
    a1i
    wph
    cF
    cP
    @3
    clm
    cfv
    wbr
    #
    @6
    @7
    wph
    cP
    cF
    @3
    @4
    c1
    cvv
    cX
    cn
    @4
    eqid
    nnuz
    @9
    @3
    ctop
    wcel
    wph
    @3
    @3
    eqid
    #
    cnfldtop
    a1i
    lmlim.p
    @11
    lmlim.f
    lmss
    wph
    @10
    cn
    cc
    cF
    wf
    #
    @12
    @7
    wb
    1z
    wph
    cn
    cX
    cF
    wf
    @8
    @14
    lmlim.f
    lmlim.x
    cn
    cX
    cc
    cF
    fss
    sylancl
    cP
    cF
    @3
    c1
    cn
    @13
    nnuz
    lmclimf
    sylancr
    bitr3d
    3bitrd
end

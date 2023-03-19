include "cvts.mm"
include "co.mm"
include "cfv.mm"
include "c1.mm"
include "cfz.mm"
include "cv.mm"
include "ci.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "ce.mm"
include "csu.mm"
include "cc.mm"
include "vtsval.mm"
include "fzfid.mm"
include "wcel.mm"
include "wa.mm"
include "cn.mm"
include "wf.mm"
include "adantr.mm"
include "wss.mm"
include "fz1ssnn.mm"
include "a1i.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "ax-icn.mm"
include "2cn.mm"
include "picn.mm"
include "mulcli.mm"
include "nncnd.mm"
include "mulcld.mm"
include "efcld.mm"
include "fsumcl.mm"
include "eqeltrd.mm"

theorem vtscl
  let wph: wff ph
  let cL: class L
  let cN: class N
  let cX: class X
  let va: setvar a
  let vl: setvar l
  let vn: setvar n
  let vx: setvar x
  assume vtsval.n: |- ( ph -> N e. NN0 )
  assume vtsval.x: |- ( ph -> X e. CC )
  assume vtsval.l: |- ( ph -> L : NN --> CC )


  assert |- ( ph -> ( ( L vts N ) ` X ) e. CC )

  proof
    wph
    cX
    cL
    cN
    cvts
    co
    cfv
    c1
    cN
    cfz
    co
    #
    va
    cv
    #
    cL
    cfv
    #
    ci
    c2
    cpi
    cmul
    co
    #
    cmul
    co
    #
    @1
    cX
    cmul
    co
    #
    cmul
    co
    #
    ce
    cfv
    #
    cmul
    co
    #
    va
    csu
    cc
    wph
    cL
    cN
    cX
    va
    vtsval.n
    vtsval.x
    vtsval.l
    vtsval
    wph
    @0
    @8
    va
    wph
    c1
    cN
    fzfid
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @2
    @7
    @10
    cn
    cc
    @1
    cL
    wph
    cn
    cc
    cL
    wf
    @9
    vtsval.l
    adantr
    wph
    @0
    cn
    @1
    @0
    cn
    wss
    wph
    cN
    fz1ssnn
    a1i
    sselda
    #
    ffvelrnd
    @10
    @6
    @10
    @4
    @5
    @4
    cc
    wcel
    @10
    ci
    @3
    ax-icn
    c2
    cpi
    2cn
    picn
    mulcli
    mulcli
    a1i
    @10
    @1
    cX
    @10
    @1
    @11
    nncnd
    wph
    cX
    cc
    wcel
    @9
    vtsval.x
    adantr
    mulcld
    mulcld
    efcld
    mulcld
    fsumcl
    eqeltrd
end

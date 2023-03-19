include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cs2.mm"
include "wf.mm"
include "cword.mm"
include "wcel.mm"
include "s2cld.mm"
include "cfzo.mm"
include "wrdf.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "cz.mm"
include "1z.mm"
include "fzval3.mm"
include "ax-mp.mm"
include "cs1.mm"
include "fveq2i.mm"
include "s1len.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "c2.mm"
include "s2len.mm"
include "df-2.mm"
include "3eqtr4i.mm"
include "a1i.mm"
include "feq2d.mm"
include "mpbird.mm"
include "syl.mm"
include "feq1i.mm"
include "sylibr.mm"

theorem 1wlkdlem1
  let wph: wff ph
  let cP: class P
  let cF: class F
  let cJ: class J
  let cV: class V
  let cX: class X
  let cY: class Y
  assume 1wlkd.p: |- P = <" X Y ">
  assume 1wlkd.f: |- F = <" J ">
  assume 1wlkd.x: |- ( ph -> X e. V )
  assume 1wlkd.y: |- ( ph -> Y e. V )


  assert |- ( ph -> P : ( 0 ... ( # ` F ) ) --> V )

  proof
    wph
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    #
    cV
    cX
    cY
    cs2
    #
    wf
    #
    @1
    cV
    cP
    wf
    wph
    @2
    cV
    cword
    wcel
    #
    @3
    wph
    cX
    cY
    cV
    1wlkd.x
    1wlkd.y
    s2cld
    @4
    @3
    cc0
    @2
    chash
    cfv
    #
    cfzo
    co
    #
    cV
    @2
    wf
    cV
    @2
    wrdf
    @4
    @1
    @6
    cV
    @2
    @1
    @6
    wceq
    @4
    cc0
    c1
    cfz
    co
    #
    cc0
    c1
    c1
    caddc
    co
    #
    cfzo
    co
    #
    @1
    @6
    c1
    cz
    wcel
    @7
    @9
    wceq
    1z
    cc0
    c1
    fzval3
    ax-mp
    @0
    c1
    cc0
    cfz
    @0
    cJ
    cs1
    #
    chash
    cfv
    c1
    cF
    @10
    chash
    1wlkd.f
    fveq2i
    cJ
    s1len
    eqtri
    oveq2i
    @5
    @8
    cc0
    cfzo
    @5
    c2
    @8
    cX
    cY
    s2len
    df-2
    eqtri
    oveq2i
    3eqtr4i
    a1i
    feq2d
    mpbird
    syl
    @1
    cV
    cP
    @2
    1wlkd.p
    feq1i
    sylibr
end

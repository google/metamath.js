include "co.mm"
include "cfv.mm"
include "cun.mm"
include "clmod.mm"
include "wcel.mm"
include "wss.mm"
include "lspssv.mm"
include "syl2anc.mm"
include "lspssid.mm"
include "lsmless1x.mm"
include "syl31anc.mm"
include "lsmless2x.mm"
include "sstrd.mm"
include "wceq.mm"
include "lsmsp2.mm"
include "syl3anc.mm"
include "sseqtrd.mm"

theorem lsmssspx
  let wph: wff ph
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cN: class N
  let cV: class V
  let cW: class W
  assume lsmsp2.v: |- V = ( Base ` W )
  assume lsmsp2.n: |- N = ( LSpan ` W )
  assume lsmsp2.p: |- .(+) = ( LSSum ` W )
  assume lsmssspx.t: |- ( ph -> T C_ V )
  assume lsmssspx.u: |- ( ph -> U C_ V )
  assume lsmssspx.w: |- ( ph -> W e. LMod )


  assert |- ( ph -> ( T .(+) U ) C_ ( N ` ( T u. U ) ) )

  proof
    wph
    cT
    cU
    c.po
    co
    #
    cT
    cN
    cfv
    #
    cU
    cN
    cfv
    #
    c.po
    co
    #
    cT
    cU
    cun
    cN
    cfv
    #
    wph
    @0
    @1
    cU
    c.po
    co
    #
    @3
    wph
    cW
    clmod
    wcel
    #
    @1
    cV
    wss
    #
    cU
    cV
    wss
    #
    cT
    @1
    wss
    #
    @0
    @5
    wss
    lsmssspx.w
    wph
    @6
    cT
    cV
    wss
    #
    @7
    lsmssspx.w
    lsmssspx.t
    cT
    cN
    cV
    cW
    lsmsp2.v
    lsmsp2.n
    lspssv
    syl2anc
    #
    lsmssspx.u
    wph
    @6
    @10
    @9
    lsmssspx.w
    lsmssspx.t
    cT
    cN
    cV
    cW
    lsmsp2.v
    lsmsp2.n
    lspssid
    syl2anc
    cV
    c.po
    cT
    @1
    cU
    cW
    clmod
    lsmsp2.v
    lsmsp2.p
    lsmless1x
    syl31anc
    wph
    @6
    @7
    @2
    cV
    wss
    #
    cU
    @2
    wss
    #
    @5
    @3
    wss
    lsmssspx.w
    @11
    wph
    @6
    @8
    @12
    lsmssspx.w
    lsmssspx.u
    cU
    cN
    cV
    cW
    lsmsp2.v
    lsmsp2.n
    lspssv
    syl2anc
    wph
    @6
    @8
    @13
    lsmssspx.w
    lsmssspx.u
    cU
    cN
    cV
    cW
    lsmsp2.v
    lsmsp2.n
    lspssid
    syl2anc
    cV
    c.po
    @1
    cU
    @2
    cW
    clmod
    lsmsp2.v
    lsmsp2.p
    lsmless2x
    syl31anc
    sstrd
    wph
    @6
    @10
    @8
    @3
    @4
    wceq
    lsmssspx.w
    lsmssspx.t
    lsmssspx.u
    c.po
    cT
    cU
    cN
    cV
    cW
    lsmsp2.v
    lsmsp2.n
    lsmsp2.p
    lsmsp2
    syl3anc
    sseqtrd
end

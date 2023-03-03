
include "wi.mm"
include "ax-1.mm"
include "mpd.mm"

theorem id
  let wph: wff ph
  assert |- ( ph -> ph )

  step 0) wph(): wff ph
  step 1) wph(): wff ph
  step 2) wph(): wff ph
  step 3) wi(1,2): wff ( ph -> ph )
  step 4) wph(): wff ph
  step 5) wph(): wff ph
  step 6) wph(): wff ph
  step 7) ax-1(5,6): |- ( ph -> ( ph -> ph ) )
  step 8) wph(): wff ph
  step 9) wph(): wff ph
  step 10) wph(): wff ph
  step 11) wi(9,10): wff ( ph -> ph )
  step 12) ax-1(8,11): |- ( ph -> ( ( ph -> ph ) -> ph ) )
  step 13) mpd(0,3,4,7,12): |- ( ph -> ph )
end
